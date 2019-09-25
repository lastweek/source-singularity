using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Threading.Tasks;
using System.Diagnostics;
using System.IO;
using System.Text.RegularExpressions;

namespace NuBuild
{
    class VSSolutionParser
    {
        private SourcePath _solutionFile;

        public VSSolutionParser(SourcePath solutionFile)
        {
            _solutionFile = solutionFile;
            _parse();
        }

        private List<BuildObject> _dependencies = new List<BuildObject>();
        private List<BuildObject> _outputs = new List<BuildObject>();

        private void _parse()
        {
            _dependencies.Add(_solutionFile);

            using (StreamReader stream = new StreamReader(_solutionFile.getFilesystemPath())) {
                Regex regex = new Regex(@"Project\([\S]+\)[\s]+=[\s]+([^$]*)", RegexOptions.IgnoreCase);
                string line;

                while ((line = stream.ReadLine()) != null) {
                    MatchCollection matches = regex.Matches(line);

                    if (matches.Count > 0)
                    {
                        SourcePath projFile = _solutionFile.getNewSourcePath(matches[0].Groups[1].Value.Split("\", ".ToCharArray())[5]);
//-                        Console.WriteLine(String.Format("Found project file {0}", projFile.getFilesystemPath()));
                        VSProjectParser proj = new VSProjectParser(projFile);
                        _dependencies.AddRange(proj.getDependencies());
                        _outputs.AddRange(proj.getOutputs());
                    }
                }

                stream.Close();
            }

        }
        public IEnumerable<BuildObject> getDependencies()
        {
            return _dependencies;
        }

        public IEnumerable<BuildObject> getOutputs()
        {
            return _outputs;
        }
    }
}
