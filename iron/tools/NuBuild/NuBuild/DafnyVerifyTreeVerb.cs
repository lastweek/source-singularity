using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Threading.Tasks;
using System.IO;
using System.Diagnostics;

namespace NuBuild
{
    class DafnyVerifyTreeVerb
        : Verb, IObligationsProducer 
    {
        SourcePath displayRoot; //- used only in labeling the output
        BuildObject obligations;
        AbstractId abstractId;

        const int version = 30;

        const string DFYTREE_EXTN = ".dfytree";

        public DafnyVerifyTreeVerb(SourcePath root)
        {
            this.displayRoot = root;
            obligations = root.makeOutputObject(DFYTREE_EXTN + VerificationObligationList.VOL_EXTN);       
            abstractId = new AbstractId(this.GetType().Name, version, root.ToString());            
        }

        public override AbstractId getAbstractIdentifier() { return abstractId; }

        public BuildObject getObligationSet() { return obligations; }

        BuildObject mkVerificationObject(BuildObject dfysource) {
            return dfysource.makeOutputObject(DafnyVerifyOneVerb.DAFNY_EXTN + VerificationResultVerb.VERIFICATION_RESULT_EXTN);
        }

        private HashSet<BuildObject> getAvailableDeps(out DependencyDisposition ddisp)
        {
            TransitiveDepsVerb depsVerb = new DafnyTransitiveDepsVerb(this.displayRoot);
            HashSet<BuildObject> availableDeps = depsVerb.getAvailableDeps(out ddisp);
            availableDeps.Add(this.displayRoot);  //- TransitiveDeps *exclude* the root, so we need to add that in, too.
            return availableDeps;
        }

        public override IEnumerable<BuildObject> getDependencies(out DependencyDisposition ddisp)
        {                              
            HashSet<BuildObject> availableDeps = getAvailableDeps(out ddisp);

            List<BuildObject> true_deps = new List<BuildObject>();
            foreach (BuildObject dep in availableDeps)
            {
                if (dep.getExtension().EndsWith(DafnyVerifyOneVerb.DAFNY_EXTN))
                {
                    true_deps.Add(mkVerificationObject(dep));
                }
                else
                {
                    true_deps.Add(dep);
                }
            }
            return true_deps;
        }

        IEnumerable<BuildObject> getDafnyDependencies(out DependencyDisposition ddisp)
        {
            HashSet<BuildObject> result = getAvailableDeps(out ddisp);
            return result.Where(dep => dep.getExtension().EndsWith(DafnyVerifyOneVerb.DAFNY_EXTN));            
        }
     
        public override IEnumerable<IVerb> getVerbs()
        {
            //- TODO cast below assumes dafny files are always source files.
            //- That's easy enough to remedy in DafnyVerifyOneVerb ctor, but for
            //- now, we continue assuming it.      
            //- This will matter if we ever auto-generate a Dafny file
            DependencyDisposition ddispDummy;
            IEnumerable<IVerb> result =  getDafnyDependencies(out ddispDummy)
                .Select(dfysource => new DafnyVerifyOneVerb((SourcePath) dfysource))
                .Concat(new List<IVerb>() {new DafnyTransitiveDepsVerb(this.displayRoot)});

            return result;
        }

        public override IEnumerable<BuildObject> getOutputs()
        {
            return new HashSet<BuildObject>() { obligations };
        }

        public override IVerbWorker getWorker() {
            IEnumerable<BuildObject> verificationResults = getVerbs()
                .Where(verb => verb is VerificationResultVerb)
                .Select(dfy_one => ((VerificationResultVerb)dfy_one).getOutputFile());
            VerificationObligationList vol = new VerificationObligationList(verificationResults);
            vol.store(this.obligations);
            return new VerbSyncWorker(new Fresh());
        }

    }
}
