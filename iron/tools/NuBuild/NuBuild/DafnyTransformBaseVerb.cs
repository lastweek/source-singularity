using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Threading.Tasks;
using System.IO;
using System.Diagnostics;

namespace NuBuild
{
    abstract class DafnyTransformBaseVerb
        : Verb, IProcessInvokeAsyncVerb
    {
        public const char DAFNY_S_SUFFIX = 's';  //- a trusted specification file
        public const char DAFNY_C_SUFFIX = 'c';  //- a checked specification file
        public const char DAFNY_I_SUFFIX = 'i';  //- a checked implementation file
        public static readonly char[] DAFNY_SUFFIXES = { DAFNY_S_SUFFIX, DAFNY_C_SUFFIX, DAFNY_I_SUFFIX };
        public static readonly string[] DAFNY_LONG_EXTNS = {
            "."+DAFNY_S_SUFFIX+DafnyVerifyOneVerb.DAFNY_EXTN,
            "."+DAFNY_C_SUFFIX+DafnyVerifyOneVerb.DAFNY_EXTN,
            "."+DAFNY_I_SUFFIX+DafnyVerifyOneVerb.DAFNY_EXTN };

        protected SourcePath dfyroot;
        protected string appLabel;        

        protected const int version = 15;
        protected const string DAFNY_PRELUDE_DIRECTORY = "tools/DafnySpec";
        protected const string DAFNY_PRELUDE_FILENAME = "DafnyPrelude.dfy";

        protected abstract int getVersion();
        protected abstract BuildObject getExecutable();        

        //- getRoots is the set of dafny files from which we explore to
        //- discover the set of dependencies. We use the same transitive
        //- closure to compute the set of allDafnyModules, which tell
        //- us what output files to expect.
        protected abstract IEnumerable<SourcePath> getRoots();
        
        //- roots -> dependencies
        //- roots -> allDafnyModules -> getRootArgs

        //- getRootArgs is the set of dafny files we hand to the executable.
        //- In the DafnyCC case, it's the transitive closure (allDafnyModules),
        //- in the DafnySpec case, it's the roots only. Weird. And there are
        //- weird exceptions in both cases.
        protected abstract IEnumerable<SourcePath> getRootArgs();

        protected virtual IEnumerable<BuildObject> getExtraDependencies()
        {
            return new BuildObject[] { };
        }
        protected virtual IEnumerable<string> getExtraSpecialOutputs()
        {
            return new string[] { };
        }
        protected virtual void addExtraArgs(List<string> args)
        {
        }
        protected virtual bool transformFilterAccepts(BuildObject dfysource)
        {
            return true;
        }

        public DafnyTransformBaseVerb(SourcePath dfyroot, string appLabel)
        {
            this.dfyroot = dfyroot;
            this.appLabel = appLabel;

            IEnumerable<string> roots = getRoots().Select(obj => obj.ToString());             
        }

        protected virtual IEnumerable<SourcePath> getAllDafnyModules(out DependencyDisposition ddisp)
        {
            HashSet<BuildObject> result = DafnyExtensions.getForestDependencies(getRoots(), out ddisp);
            //- now we assert that all Dafny inputs are actually SourcePaths.
            HashSet<SourcePath> rc = new HashSet<SourcePath>();
            foreach (BuildObject obj in result)
            {
                if (obj.getExtension().EndsWith(DafnyVerifyOneVerb.DAFNY_EXTN))
                {
                    rc.Add((SourcePath)obj);
                }
                else
                {
                    Util.Assert(obj.getExtension().EndsWith(TransitiveDepsVerb.TDEP_EXTN));
                    //- discard it.
                }
            }
            return rc;
        }

        public override IEnumerable<BuildObject> getDependencies(out DependencyDisposition ddisp)
        {
            HashSet<BuildObject> result = DafnyExtensions.getForestDependencies(getRoots(), out ddisp);
            result.Add(getExecutable());
            result.UnionWith(getExtraDependencies());
            return result;
        }

        public override IEnumerable<IVerb> getVerbs()
        {
            return DafnyExtensions.getForestVerbs(getRoots());
        }

        string getDestPath()
        {
            //- This logic duplicates BuildObject.makeLabeledOutputObject; the interface isn't tidily
            //- factored for reuse yet.
            string path = this.GetType().Name;
            if (appLabel != null)
            {
                path = Path.Combine(appLabel, path);
            }
            path = Path.Combine(BuildEngine.theEngine.getObjRoot(), path);
            return path;
        }

        BuildObject basmOutputForDafnyModule(string modulename, string extn)
        {
            bool isTrusted = 
                (modulename.EndsWith("_"+DAFNY_S_SUFFIX)
                || modulename.Equals("Trusted"))
                && BeatExtensions.whichPart(extn) == ModPart.Imp;
            return new BuildObject(Path.Combine(getDestPath(), modulename + extn), isTrustedArg:isTrusted);
        }

        public class InOutMapping {
            public readonly BuildObject dfysource;  //- null --> outputs come from bowels of DafnySpec/DafnyCC.
            public readonly BuildObject basmIfc;
            public readonly BuildObject basmImp;
            public InOutMapping(BuildObject dfysource, BuildObject basmIfc, BuildObject basmImp)
            {
                this.dfysource = dfysource;
                this.basmIfc = basmIfc;
                this.basmImp = basmImp;
            }
        }

        private delegate void Tacker(BuildObject dfysource, string filename);
        private List<InOutMapping> getInOutMappings()
        {
            List<InOutMapping> mapping = new List<InOutMapping>();
            Tacker tack = delegate(BuildObject dfysource, string filename)
            {
                mapping.Add(new InOutMapping(
                    dfysource,
                    basmOutputForDafnyModule(filename, BoogieAsmVerifyVerb.BASMIFC_EXTN),
                    basmOutputForDafnyModule(filename, BoogieAsmVerifyVerb.BASMIMP_EXTN)));
            };

            DependencyDisposition ddispDummy;
            foreach (SourcePath dfy in getAllDafnyModules(out ddispDummy))
            {
                //- Trim off ".dfy" but not ".s" or ".i"
                string dfyname = dfy.getFileName();
                Util.Assert(dfyname.EndsWith(".dfy"));
                string basename = dfyname.Substring(0, dfyname.Length - 4);
                Util.Assert(basename.Equals(dfy.getFileNameWithoutExtension()));    //- TODO delete prior lines.

                basename = Util.dafnySpecMungeName(basename);
                if ((this is DafnyCCVerb)
                    && (basename.Equals("Seq") || basename.Equals("Seq_s")))
                {   //- TODO undesirable workaround -- DafnyCC doesn't want 'seq.dfy' in its output list, but DafnySpec does...?
                    continue;
                }
                tack(dfy, "dafny_" + basename);
            }
            tack(null, "Trusted");    //- DafnyCC doesn't really want this, but meh, it emits it, so we account for it.
            foreach (string basename in getExtraSpecialOutputs())
            {
                tack(null, basename);
            }
            return mapping;
        }

        public override IEnumerable<BuildObject> getOutputs()
        {

            List<BuildObject> outputs = new List<BuildObject>();
            foreach (InOutMapping mapping in getInOutMappings())
            {
                if (mapping.dfysource==null
                    || mapping.dfysource.Equals(getDafnyPrelude())
                    || transformFilterAccepts(mapping.dfysource))
                {
                    outputs.Add(mapping.basmIfc);
                    outputs.Add(mapping.basmImp);
                }
            }
            outputs.Add(new BuildObject(Path.Combine(
                getDestPath(), "dafny_modules.txt")));
            return outputs;
        }        

        string getAbsDestPath()
        {
            return Path.Combine(BuildEngine.theEngine.getIronRoot(), getDestPath());
        }

        public override IVerbWorker getWorker()
        {
            string absDestPath = getAbsDestPath();
            Directory.Delete(absDestPath, true); //- This verb should be the only one writing here, so let's keep it tidy.
            Directory.CreateDirectory(absDestPath);
            string dafnyccExecutable = getExecutable().getRelativePath();

            List<string> args = new List<string>();
            args.AddRange(getRootArgs().Select<SourcePath,string>(sp => sp.getRelativePath()));
            args.Add("/outdir:" + getDestPath());
            addExtraArgs(args);

            return new ProcessInvokeAsyncWorker(this,
                dafnyccExecutable, args.ToArray(), ProcessInvoker.RcHandling.NONZERO_RC_IS_FAILURE, getDiagnosticsBase());
        }

        public Disposition complete(ProcessInvokeAsyncWorker worker)
        {
            if (worker.pinv.disposition is Failed)
            {
                return worker.pinv.disposition;
            }
            
            HashSet<string> createdFiles = new HashSet<string>(Directory.GetFiles(getAbsDestPath()).Select(path => Path.GetFileName(path)));
            HashSet<string> expectedFiles = new HashSet<string>(getOutputs().Select(obj => obj.getFileName()));

            //- DafnyCC/DafnySpec process a big batch of files together. Verify that we correctly modeled what it did.
            if (!createdFiles.SetEquals(expectedFiles))
            {
                bool dummy = createdFiles.SetEquals(expectedFiles);
                int missing = expectedFiles.Except(createdFiles).Count();
                int extra = createdFiles.Except(expectedFiles).Count();
                string msg = "Missing files: " + String.Join(",", expectedFiles.Except(createdFiles)) + "\n" +
                    "  Extra files: " + String.Join(",", createdFiles.Except(expectedFiles));
                return new Failed(msg);
            }

            //- Propagate the NuBuild annotations.
            foreach (InOutMapping mapping in getInOutMappings())
            {
                if (mapping.dfysource != null
                    && transformFilterAccepts(mapping.dfysource))
                {
                    AnnotationScanner.transferAnnotations(
                        mapping.dfysource, mapping.basmIfc, BoogieAsmDepBase.CommentSymbol);
                    AnnotationScanner.transferAnnotations(
                        mapping.dfysource, mapping.basmImp, BoogieAsmDepBase.CommentSymbol);
                }
            }

            return new Fresh();;
        }
   
        protected SourcePath getDafnyPrelude()
        {
            return new SourcePath(Path.Combine(DAFNY_PRELUDE_DIRECTORY, DAFNY_PRELUDE_FILENAME), SourcePath.SourceType.sourceTypeTools);
        }
    }
}
