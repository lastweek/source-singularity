using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Threading.Tasks;
using System.Diagnostics;
using System.IO;
using System.Text.RegularExpressions;
using System.Xml;

namespace NuBuild
{
    class VSProjectParser
    {
        private SourcePath _projectFile;

        public VSProjectParser(SourcePath projectFile)
        {
            _projectFile = projectFile;
            _parse();

            CustomManifestParser cm = new CustomManifestParser(_projectFile);
            _dependencies.UnionWith(cm.getDependencies());
            _outputs.UnionWith(cm.getOutputs());
        }

        private HashSet<BuildObject> _dependencies = new HashSet<BuildObject>();
        private HashSet<BuildObject> _outputs = new HashSet<BuildObject>();

        private void _parse()
        {
            _dependencies.Add(_projectFile);

            using (XmlTextReader reader = new XmlTextReader(_projectFile.getFilesystemPath()))
            {
                while (reader.Read())
                {
                    if (reader.NodeType == XmlNodeType.Element)
                    {
                        if (String.Compare(reader.Name, "Compile") == 0)
                        {
                            _dependencies.Add(_projectFile.getNewSourcePath(reader.GetAttribute("Include")));
                        }
                        else if (String.Compare(reader.Name, "PropertyGroup") == 0)
                        {
                            _parseOutput(reader);
                        }
                    }

                }

                reader.Close();
            }

            if (_outputType != null && _assemblyName != null) //- && _outputPath != null)
            {
                string path = Path.Combine(_projectFile.getDirPath(), String.Format("{0}.{1}", _assemblyName, outputTypeToExtension(_outputType)));
                //-Console.WriteLine("{0}: generating {1}", _projectFile.getRelativePath(), path);
                _outputs.Add(new BuildObject(path));
            }
            else
            {
                throw new UserError(String.Format("Project {0} doesn't seem to have output specification in the expected format", _projectFile.getRelativePath()));
            }
        }


        private string _outputType = null;
        private string _assemblyName = null;
//-        private string _outputPath = null;

        private void _validateConsistentOption(string optionName, string oldValue, string newValue)
        {
            if (oldValue == null)
                return;

            if (!oldValue.Equals(newValue))
            {
                throw new UserError(String.Format("Values for {0} not consistent across all build configurations in {1} ({2} vs {3})",
                    optionName, _projectFile.getRelativePath(), oldValue, newValue));
            }
        }

        private void _parseOutput(XmlTextReader reader)
        {
            string lastElement = null;

            while (reader.Read())
            {
                if (reader.NodeType == XmlNodeType.EndElement)
                {
                    lastElement = null;

                    if ("PropertyGroup".Equals(reader.Name))
                    {
                        break;
                    }
                }

                if (reader.NodeType == XmlNodeType.Element)
                {
                    lastElement = reader.Name;
                }

                if (reader.NodeType == XmlNodeType.Text && lastElement != null)
                {
                    string val = reader.Value;

//-                    if ("OutputPath".Equals(lastElement))
//-                    {
//-                        _validateConsistentOption("OutputPath", _outputPath, val);
//-                        _outputPath = val;
//-                    }
                    if ("AssemblyName".Equals(lastElement))
                    {
                        _validateConsistentOption("AssemblyName", _assemblyName, val);
                        _assemblyName = val;
                    }
                    if ("OutputType".Equals(lastElement))
                    {
                        _validateConsistentOption("OutputType", _outputType, val);
                        _outputType = val;
                    }
                }
            }

        }

        private string outputTypeToExtension(string outputType)
        {
            if (outputType == "Exe")
            {
                return "exe";
            }
            else
            {
                throw new SourceConfigurationError("VSProjectParser doesn't know how to canonicalize "+outputType);
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
}}