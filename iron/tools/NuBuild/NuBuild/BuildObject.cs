using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Threading.Tasks;
using System.IO;
using System.Diagnostics;

namespace NuBuild
{
    class BuildObject
    {
                //- Path stored relative to "iron", so it begins either with "src" or "obj"
        protected string path;
        protected bool _isTrusted;

        public bool isTrusted { get { return _isTrusted; } }

        public BuildObject(string inpath, bool isTrustedArg = false)
        {
            Util.Assert(!inpath.StartsWith(BuildEngine.theEngine.getSrcRoot()));
            this.path = BuildEngine.theEngine.normalizeIronPath(inpath);
            _isTrusted = isTrustedArg;
        }

        protected enum IsSourcePath { Yep };
        protected BuildObject(string inpath, IsSourcePath isSourcePath)
        {
            this.path = BuildEngine.theEngine.normalizeIronPath(inpath);
        }

        public string getRelativePath()
        {
            return path;
        }

        public override string ToString()
        {
            return path;
        }

        public virtual string getFilesystemPath()
        {
            return Path.Combine(BuildEngine.theEngine.getIronRoot(), path);
        }

        public virtual string getFilesystemDirPath()
        {
            return Path.Combine(BuildEngine.theEngine.getIronRoot(), getDirPath());
        }

        public string getDirPath()
        {
            return Path.GetDirectoryName(path);
        }

        public string getAbsoluteDirPath()
        {
            return Path.GetDirectoryName(getFilesystemPath());
        }

        public string getFileName()
        {
            return Path.GetFileName(path);
        }

        string fn_wo_extn;
        string extn;

        void splitExtn()
        {
            if (fn_wo_extn == null)
            {
                string fn = getFileName();
                int dot = fn.IndexOf('.');
                if (dot < 0)
                {
                    fn_wo_extn = fn;
                    extn = null;
                }
                else
                {
                    extn = fn.Substring(dot);
                    //- TODO this is a (possibly brittle) workaround for dfy .s and .i,
					//- which aren't part of the file type, they're part of the name. Sorta.
                    if (DafnyTransformBaseVerb.DAFNY_LONG_EXTNS.Contains(extn))
                    {
                        dot += 2;
                        extn = fn.Substring(dot);
                    }
                    fn_wo_extn = fn.Substring(0, dot);
                }
            }
        }

        public string getFileNameWithoutExtension()
        {
            splitExtn();
            return fn_wo_extn;
        }

        public string getExtension()
        {
            splitExtn();
            return extn;
        }

        public override bool Equals(object obj)
        {
            if (obj is BuildObject)
            {
                return path.Equals(((BuildObject)obj).path);
            }
            else
            {
                return false;
            }
        }

        public override int GetHashCode()
        {
            return path.GetHashCode();
        }

        public virtual void prepareObjDirectory()
        {
            Directory.CreateDirectory(Path.GetDirectoryName(getFilesystemPath()));
        }

        //- Strip off the initial 'src\' or 'obj\' from the path, so we can plop this guy into obj\.
        private string getDirRelativeToSrcOrObj()
        {
            string dirname = getDirPath();
            int slash = dirname.IndexOf('\\');
            Util.Assert(slash >= 0);
            return dirname.Substring(slash + 1);
        }

        public BuildObject makeOutputObject(string extension)
        {
            return new BuildObject(mashedPathname(BuildEngine.theEngine.getObjRoot(), extension));
        }
        public BuildObject makeLabeledOutputObject(string appLabel, string extension)
        {
            string appSpecificPrefix =
                appLabel==null
                ? BuildEngine.theEngine.getObjRoot()
                :                 Path.Combine(BuildEngine.theEngine.getObjRoot(), appLabel);
            if (path.StartsWith(appSpecificPrefix))
            {
                //- Input is already in the correct subtree; don't nest subtrees.
                return makeOutputObject(extension);
            }
            else
            {
                //- Input is coming from elsewhere; give it a parallel location under app-specific subtree
                return new BuildObject(mashedPathname(appSpecificPrefix, extension));
            }
        }

        public BuildObject makeVirtualObject(string extension)
        {
            return new VirtualBuildObject(mashedPathname(BuildEngine.theEngine.getVirtualRoot(), extension));
        }

        private string mashedPathname(string root, string extension)
        {
            string filename = getFileNameWithoutExtension();
            filename = Util.dafnySpecMungeName(filename); //- remap dafny filenames so resulting objects have correctly-parsed extns.
            return Path.Combine(root, getDirRelativeToSrcOrObj(), filename + extension);
        }
    }
}
