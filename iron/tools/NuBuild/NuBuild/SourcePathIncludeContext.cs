using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Threading.Tasks;
using System.IO;

namespace NuBuild
{
    //- This context looks for files in a set of source path locations.
    class SourcePathIncludeContext
        : IncludePathContext
    {
        class DirectoryRecord
        {
            readonly string _directory;
            readonly HashSet<string> _files;

            public string directory { get { return _directory; } }
            public bool Contains(string file) { return _files.Contains(file); }
            public DirectoryRecord(string directory)
            {
                this._directory = directory;
                string absDir = Path.Combine(
                            BuildEngine.theEngine.getIronRoot(),
                            BuildEngine.theEngine.getSrcRoot(),
                            _directory);
                _files = new HashSet<string>(Directory.EnumerateFiles(absDir)
                    .Select(path => Path.GetFileName(path)));
            }
        }
        List<DirectoryRecord> directories;
        List<string> dstExtensions;
        string _descr;
        public SourcePathIncludeContext()
        {
            directories = new List<DirectoryRecord>();
            dstExtensions = new List<string>();
        }

        public override string ToString()
        {
            if (_descr == null)
            {
                _descr = "{" + String.Join(",", directories.Select(d => d.directory)) + "}; {"
                    + String.Join(",", dstExtensions) + "}";
            }
            return _descr;
        }

        //- add a directory path relative to ironRoot
        public void addDirectory(string directory)
        {
            Util.Assert(_descr == null);
            directories.Add(new DirectoryRecord(directory));
        }

        public void addDstExtension(string extension)
        {
            Util.Assert(_descr == null);
            dstExtensions.Add(extension);
        }

        public override BuildObject search(string basename, ModPart modPart)
        {
            List<SourcePath> results = new List<SourcePath>();

            foreach (string extension in dstExtensions.Where(extn => BeatExtensions.whichPart(extn) == modPart))
            {
                string filename = basename + extension;
                foreach (DirectoryRecord directoryRecord in directories)
                {
                    if (directoryRecord.Contains(filename))
                    {
                        string proposed = Path.Combine(
                            BuildEngine.theEngine.getIronRoot(),
                            BuildEngine.theEngine.getSrcRoot(),
                            directoryRecord.directory,
                            basename + extension);
                        //-Logger.WriteLine("SourcePathIncludeContext Trying " + proposed);
                        //-Util.Assert(File.Exists(proposed));
                        results.Add(new SourcePath(proposed));
                    }
                }
            }
            if (results.Count() == 0)
            {
                return null;
            }
            else if (results.Count() > 1)
            {
                throw new SourceConfigurationError(String.Format(
                    "Reference {0} matches {1} paths: {2}",
                    basename,
                    results.Count(),
                    String.Join(",", results)));
            }
            else
            {
                return results.First();
            }
        }

    }
}
