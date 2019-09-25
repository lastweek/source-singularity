using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Threading.Tasks;
using System.IO;
using System.Diagnostics;

namespace NuBuild
{
    //- Needs to:
    //- 1) Build the bootloader into pxeloader
    //- 2) Build two IroncladApps: Loader and specified app
    //-    Do this via a Batch
    //- 3) Create a boot.ini

    class BootableAppVerb
        : Verb
    {
        const int version = 4;
        public const string BOOT_EXTN = ".ini";
        public const string LOADER_DFY = "src\\Dafny\\Apps\\AppLoader\\Main.i.dfy";

        SourcePath dfyroot;
        AbstractId abstractId;
        VerificationRequest verificationRequest;

        //- Dependencies
        BuildObject bootloader = new SourcePath("obj/Checked/BootLoader/pxe-loader", SourcePath.SourceType.sourceTypePrebakedObjExpediency);

        //- Outputs
        BuildObject bootIniFile;
        BuildObject loaderCopy;
        BuildObject bootloaderCopy;
        BuildObject appExecutableCopy;

        //- Intermediate verbs
        IroncladAppVerb loaderVerb;
        IroncladAppVerb appVerb;
        BatchVerifyVerb batchVerb;
        VerificationResultSummaryVerb batchSummaryVerb;

        public BootableAppVerb(SourcePath dfyroot, DafnyCCVerb.FramePointerMode useFramePointer, VerificationRequest verificationRequest)
        {
            this.dfyroot = dfyroot;
            this.verificationRequest = verificationRequest;
            string concreteId = verificationRequest.ToString() + "," + useFramePointer.ToString();
            this.abstractId = new AbstractId(this.GetType().Name, version, dfyroot.ToString(), concrete: concreteId);
 
            string targetDirectory = Path.Combine(BuildEngine.theEngine.getObjRoot(), dfyroot.getDirPath(),
                "bootable-" + verificationRequest.ToString());
            bootIniFile = new BuildObject(Path.Combine(targetDirectory, "safeos/boot.ini"));
        
            //- TODO: Create the bootloader verb

            loaderVerb = new IroncladAppVerb(new SourcePath(LOADER_DFY), IroncladAppVerb.TARGET.BARE_METAL, useFramePointer, verificationRequest);
            appVerb = new IroncladAppVerb(dfyroot, IroncladAppVerb.TARGET.BARE_METAL, useFramePointer, verificationRequest);

            batchVerb = new BatchVerifyVerb(dfyroot, new HashSet<IObligationsProducer>() { appVerb, loaderVerb }, BatchVerifyVerb.BatchMode.APP);
            batchSummaryVerb = new VerificationResultSummaryVerb(batchVerb);

            loaderCopy = new BuildObject(Path.Combine(targetDirectory, targetExecutableName(loaderVerb)));
            bootloaderCopy = new BuildObject(Path.Combine(targetDirectory, bootloader.getFileName()));
            appExecutableCopy = new BuildObject(Path.Combine(targetDirectory, targetExecutableName(appVerb)));
        }

        private string targetExecutableName(IroncladAppVerb fromVerb)
        {
            //- It's okay that we're saving an unverified binary to a .exe extension, because it's
            //- getting placed inside targetDirectory, which is labeled "bootable-unverified."
            return fromVerb.getAppLabel() + IroncladAppVerb.TRUSTED_EXE_EXTN;
        }

        public override IEnumerable<BuildObject> getDependencies(out DependencyDisposition ddisp)
        {
            List<BuildObject> result = new List<BuildObject>();
            //-result.Add(bootloader);  
            result.Add(loaderVerb.getExe());
            result.Add(appVerb.getExe());

            result.AddRange(batchSummaryVerb.getOutputs());

            ddisp = DependencyDisposition.Complete;                    
            return result;
        }

        string mkBootFileEntry(BuildObject obj) 
        {
            return String.Format("Size={0}   Path=/{1}", new FileInfo(obj.getFilesystemPath()).Length, obj.getFileName());
        }

        void writeBootFile() 
        {
            List<string> lines = new List<string>();

            lines.Add(mkBootFileEntry(loaderCopy));
            lines.Add(mkBootFileEntry(appExecutableCopy));

            File.WriteAllLines(bootIniFile.getFilesystemPath(), lines);
        }

        public override IVerbWorker getWorker() {

            if (verificationRequest.isComplete())
            {
                VerificationResult vr = VerificationResult.fromXmlFile(batchSummaryVerb.getOutputFile().getRelativePath());

                if (!vr.pass)
                {
                    Util.Assert(false);     //- Should never get here, since Ironclad app should fail before producing a verified exe
                    return new VerbSyncWorker(new Failed());
                }
            }

            //- Copy the AppLoader binary and the bootloader into the same directory as the app's binary, so the pxe-loader can find them
            File.Copy(loaderVerb.getExe().getFilesystemPath(), loaderCopy.getFilesystemPath(), true);
            File.Copy(appVerb.getExe().getFilesystemPath(), appExecutableCopy.getFilesystemPath(), true);
            File.Copy(bootloader.getFilesystemPath(), bootloaderCopy.getFilesystemPath(), true);
            
            writeBootFile();
            return new VerbSyncWorker(new Fresh());
        }

        public override IEnumerable<IVerb> getVerbs()
        {
            List<IVerb> result = new List<IVerb>();
            //-result.Add(bootloaderVerb);             
            result.Add(batchSummaryVerb);
            result.Add(appVerb);
            result.Add(loaderVerb);

            return result;
        }

        public override IEnumerable<BuildObject> getOutputs()
        {
            return new BuildObject[] { bootIniFile, loaderCopy, bootloaderCopy };
        }

        public override AbstractId getAbstractIdentifier()
        {
            return abstractId;
        }

        public override Presentation getPresentation()
        {
            return batchSummaryVerb.getPresentation();
        }
    }
}
