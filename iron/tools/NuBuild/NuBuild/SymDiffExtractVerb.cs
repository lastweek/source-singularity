using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Threading.Tasks;
using System.IO;

namespace NuBuild
{
    class SymDiffExtractVerb : SymDiffBaseVerb
    {
        //-public const string UNROLLED_EXTN = ".unrolled";
        //-public const string LEFT_EXTN = ".left";
        //-public const string RIGHT_EXTN = ".right";  
        public const string LEFT_EXTN = "_left";
        public const string RIGHT_EXTN = "_right"; 

        const int version = 4;
        
        AbstractId abstractId;
        BoogieAsmVerifyVerb basmVerb;
        BuildObject basmIn;
        Mode mode;

        public enum Mode { LEFT, RIGHT };

        public SymDiffExtractVerb(BoogieAsmVerifyVerb basmVerb, Mode mode)
        {
            this.basmVerb = basmVerb;
            this.basmIn = basmVerb.outputFile();
            this.mode = mode;

            abstractId = new AbstractId(this.GetType().Name, version, basmIn.ToString(), concrete:mode.ToString());                            
        }
        public override IEnumerable<BuildObject> getInputFiles()
        {
            return new List<BuildObject>() {basmIn};
        }

        public override BuildObject getOutputFile()
        {
            string extension = null;
            switch (mode)
            {
                case Mode.LEFT:
                    extension = LEFT_EXTN; break;                               
                case Mode.RIGHT:
                    extension = RIGHT_EXTN; break;              
                default:
                    throw new Exception("Unexpected mode for SymDiffExtractVerb");                    
            }
            return new BuildObject(Path.Combine(basmIn.getDirPath(), basmIn.getFileNameWithoutExtension() + extension + BoogieVerb.BPL_EXTN));
            //-return basmIn.makeOutputObject(extension + BoogieVerb.BPL_EXTN);         
        }
        
        public override AbstractId getAbstractIdentifier() { return abstractId; }       

        public override IEnumerable<IVerb> getVerbs()
        {
            return new List<IVerb>() { basmVerb };
        }

        public override IEnumerable<BuildObject> getOutputs()
        {
            return new List<BuildObject>() { getOutputFile() };
        }

        protected override List<string> getArgs()
        {
            List<string> args = new List<string>();
            args.Add("-extractLoops");
            args.Add(basmIn.getRelativePath());
            args.Add(getOutputFile().getRelativePath());

            return args;
        }     
    }
}
