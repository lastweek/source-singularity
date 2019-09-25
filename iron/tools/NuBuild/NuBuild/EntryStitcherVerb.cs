using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Threading.Tasks;
using System.IO;

namespace NuBuild
{
    class EntryStitcherVerb
        : Verb
    {
        string appLabel;
        IContextGeneratingVerb context;    //- Label our abstractIdentifier
        BeatVerb mainBeatVerb;
        SourcePath genericStitch;
        SourcePath appSpecificStitch;

        BuildObject dafnyMainImpInput;
        BuildObject dafnyMainIfcInput;
        SourcePath entryImpInput;

        const int version = 10;
        const string SENTINEL_APP_SPECIFIC_GOES_HERE = "//- SENTINEL_APP_SPECIFIC_GOES_HERE";

        public override AbstractId getAbstractIdentifier()
        {
            return new AbstractId(this.GetType().Name, version, genericStitch.ToString(), concrete:appLabel);
        }

        public EntryStitcherVerb(IContextGeneratingVerb context, string appLabel)
        {
            this.appLabel = appLabel;
            this.context = context;
            entryImpInput = new SourcePath("src/Checked/Nucleus/Main/Entry.imp.beat");
            SourcePath mainBeatSrc = new SourcePath("src/Checked/Nucleus/Main/Main.ifc.beat");
            mainBeatVerb = new BeatVerb(context, mainBeatSrc, appLabel);
            genericStitch = new SourcePath("src/Trusted/Spec/Entry.ifc.basm.stitch");
            appSpecificStitch = new SourcePath(String.Format("src/Trusted/Spec/{0}/AppRequirements.ifc.stitch", appLabel));
        }

        public override IEnumerable<BuildObject> getDependencies(out DependencyDisposition ddisp)
        {
            ddisp = DependencyDisposition.Complete;

            OrderPreservingSet<BuildObject> deps = new OrderPreservingSet<BuildObject>();

            //- Things we need to stitch the interface:
            deps.Add(genericStitch);
            deps.Add(appSpecificStitch);
            deps.AddRange(mainBeatVerb.getOutputs());

            //- Things we need to stitch the imports into the imp file:
            deps.Add(entryImpInput);
            deps.Add(context.getContextOutput());
            IIncludePathContext pathContext = context.fetchIfAvailable(ref ddisp);
            if (pathContext!=null)
            {
                dafnyMainIfcInput = pathContext.search("dafny_Main_i", ModPart.Ifc);
                Util.Assert(dafnyMainIfcInput != null);
                deps.Add(dafnyMainIfcInput);
                dafnyMainImpInput = pathContext.search("dafny_Main_i", ModPart.Ifc);
                Util.Assert(dafnyMainImpInput != null);
                deps.Add(dafnyMainImpInput);
            }
            return deps;
        }

        public override IEnumerable<IVerb> getVerbs()
        {
            return new IVerb[] { mainBeatVerb, context };
        }

        BuildObject getIfcOutput()
        {
            //- TODO will probably require parameterization per app
            return new SourcePath("src/Trusted/Spec/EntryStitched.x").makeLabeledOutputObject(appLabel, BoogieAsmVerifyVerb.BASMIFC_EXTN);
        }

        //- We also have to stitch the imp, to borrow the private-import list from dafny_Main.
        internal BuildObject getEntryImpOutput()
        {
            return new SourcePath("src/Checked/Nucleus/Main/EntryStitched.x").makeLabeledOutputObject(appLabel, BeatExtensions.BEATIMP_EXTN);
        }

        public override IEnumerable<BuildObject> getOutputs()
        {
            return new BuildObject[] { getIfcOutput(), getEntryImpOutput() };
        }

        private static IEnumerable<string> extractImportStatements(BuildObject obj)
        {
            //- Well, it might be nice to use BeatExtensions.propagatePrivateImports, but that requires
            //- a context to interpret the input imports. We don't really want to cons up yet ANOTHER
            //- intermediate context, so here's a temporary workaround. Caution; may be brittle.
            IEnumerable<string> imports = File.ReadAllLines(obj.getFilesystemPath())
                .Where(line => line.Contains("private-import"));

            //- Note that dafny_Main_i didn't really expect us to steal its
            //- imports, so it hasn't conditioned the Checked and Trusted imports to be beat-resistant.
            imports = imports.Select(
                line => line.Contains("Checked") || line.Contains("Trusted")
                ? line.Replace("private-import", "private-basmonly-import")
                : line);
            return imports;
        }
        public override IVerbWorker getWorker()
        {
            //- Mimic this line from src/Checked/Nucleus/Main/build.ps1:
            //- _cat    -out $OBJ\EntryCP_i.bpl             -in $OBJ\MainCP_i.bpl,$SPEC_OBJ\EntryCP_i.bpl
            //- TODO eliminate this special-case workaround.
            try
            {
                //- This is the trusted bit, creating the stitched ifc file.
                //-IEnumerable<string> ifcImports = extractImportStatements(dafnyMainIfcInput);
                string[] mainLines = File.ReadAllLines(mainBeatVerb.getOutputs().First().getFilesystemPath());
                string[] entryLines = File.ReadAllLines(genericStitch.getFilesystemPath());
                int sentinel_index = Array.IndexOf(entryLines, SENTINEL_APP_SPECIFIC_GOES_HERE);
                if (sentinel_index<0)
                {
                    throw new UserError("Sentinel string missing in " + genericStitch);
                }
                IEnumerable<string> entryPrologue = entryLines.Take(sentinel_index+1);
                IEnumerable<string> entryEpilogue = entryLines.Skip(sentinel_index+1);
                string[] appSpecificLines = File.ReadAllLines(appSpecificStitch.getFilesystemPath());
                //-File.WriteAllLines(getIfcOutput().getFilesystemPath(), ifcImports.Concat(mainLines.Concat(entryLines)));
                File.WriteAllLines(getIfcOutput().getFilesystemPath(),
                    mainLines.Concat(entryPrologue).Concat(appSpecificLines).Concat(entryEpilogue));

                //- Here's some (at least untrusted) workaround, snarfing and repurposing the
                //- import list from dafny_Main_i up to Entry.imp.
                IEnumerable<string> impImports = extractImportStatements(dafnyMainImpInput);
                string[] intext = File.ReadAllLines(entryImpInput.getFilesystemPath());
                File.WriteAllLines(getEntryImpOutput().getFilesystemPath(), impImports.Concat(intext));

                return new VerbSyncWorker(new Fresh());
            }
            catch (IOException ex)
            {
                return new VerbSyncWorker(new Failed(ex.ToString()));
            }
        }
    }
}
