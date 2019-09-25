using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Threading.Tasks;
using System.IO;

namespace NuBuild
{
    class CustomManifestParser
    {
        private HashSet<BuildObject> _dependencies = new HashSet<BuildObject>();
        private HashSet<BuildObject> _outputs = new HashSet<BuildObject>();

        public CustomManifestParser(SourcePath basePath)
        {
            _parseCustomManifest(basePath);
        }

        public IEnumerable<BuildObject> getDependencies()
        {
            return _dependencies;
        }

        public IEnumerable<BuildObject> getOutputs()
        {
            return _outputs;
        }

        public void _parseCustomManifest(SourcePath basePath)
        {
            SourcePath manifest = basePath.getNewSourcePath("nubuild-manifest.txt");
            _dependencies.Add(manifest);

            using (StreamReader stream = new StreamReader(manifest.getFilesystemPath()))
            {
                string origline;

                while ((origline = stream.ReadLine()) != null)
                {
                    string line = origline.Trim();

                    if (line.Length == 0)
                        continue;

                    if (line.Substring(0, 1) == "#")
                        continue;

                    string[] parts = line.Split();

                    if (parts.Length != 2) {
                        throw new UserError(String.Format("{0}: badly formed manifest line {1}", manifest.getFilesystemPath(), origline));
                    }

                    if ("output".Equals(parts[0])) {
                        _outputs.Add(new BuildObject(Path.Combine(basePath.getDirPath(), parts[1])));
                    }
                    else if ("dependency".Equals(parts[0]))
                    {
                        _dependencies.Add(basePath.getNewSourcePath(parts[1]));
                    }
                }
            }
        }
    }
}
