using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Threading.Tasks;
using System.Text.RegularExpressions;
using System.IO;

namespace NuBuild
{
    class AnnotationScanner
    {
        BuildObject inputObject;
        List<string[]> annotations;
        bool _fixed;

        //- Constructor for emitting new/code-assembled annotations
        public AnnotationScanner()
        {
            inputObject = null;
            annotations = new List<string[]>();
        }

        public void addAnnotation(string[] annotation)
        {
            Util.Assert(!_fixed);
            annotations.Add(annotation);
        }

        public AnnotationScanner(BuildObject inputObject)
        {
            this.inputObject = inputObject;
            this.annotations = new List<string[]>();
            Regex re = new Regex("<NuBuild([^>]*)/>");
            using (TextReader tr = BuildEngine.theEngine.getNuObjContents().openRead(inputObject))
            {
                while (true)
                {
                    String line = tr.ReadLine();
                    if (line == null)
                    {
                        break;
                    }
                    Match match = re.Match(line);
                    if (match.Success)
                    {
                        string[] arguments = match.Groups[1].ToString().Split(null).Where(s => s.Length > 0).ToArray();
                        annotations.Add(arguments);
                    }
                }
            }
            _fixed = true;
        }

        public string emit(string commentToken)
        {
            _fixed = true;
            StringBuilder sb = new StringBuilder();
            foreach (string[] annotation in annotations)
            {
                sb.AppendLine(commentToken + "<NuBuild " + String.Join(" ", annotation) + " />");
            }
            return sb.ToString();
        }

        public IEnumerable<string[]> getAnnotations(string label)
        {
            return annotations.Where(sa => sa[0].Equals(label));
        }

        //- Look for 0 or 1 instance of a single-valued annotation.
        public string getTheAnnotation(string label, string defaultValue)
        {
            IEnumerable<string[]> anns = getAnnotations(label);
            if (anns.Count() == 0)
            {
                return defaultValue;
            }
            string[] ann = anns.First();
            if (ann.Length != 2)
            {
                throw new SourceConfigurationError(
                    String.Format("Annotation {0} in file {1} should have exactly one argument",
                        ann[0], inputObject.getRelativePath()));
            }
            return ann[1];
        }

        internal static void transferAnnotations(BuildObject source, BuildObject dest, string commentToken)
        {
            new AnnotationScanner(source).injectAnnotations(dest, commentToken);
        }

        internal void injectAnnotations(BuildObject dest, string commentToken)
        {
            string annotations = emit(commentToken);
            string destStr = File.ReadAllText(dest.getFilesystemPath());
            File.Delete(dest.getFilesystemPath());
            File.WriteAllText(dest.getFilesystemPath(), annotations + destStr);
        }
    }
}
