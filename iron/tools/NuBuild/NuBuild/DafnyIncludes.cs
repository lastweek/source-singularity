using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Threading.Tasks;
using System.IO;
using System.Text.RegularExpressions;
using System.Diagnostics;

namespace NuBuild
{
    class DafnyIncludes
        : IIncludeFactory
    {
        public DafnyIncludes()
        {
        }

        public IEnumerable<BuildObject> getIncludes(BuildObject dfysource)
        {
            List<BuildObject> outlist = new List<BuildObject>();
            Regex re = new Regex("^\\s*include\\s*\"(.*)\"");
            using (TextReader tr = BuildEngine.theEngine.getNuObjContents().openRead(dfysource))
            {
                while (true)
                {
                    String line = tr.ReadLine();
                    if (line == null)
                    {
                        break;
                    }
                    Match match = re.Match(line);
                    int count = 0;
                    while (match.Success)
                    {
                        string includedPath = match.Groups[1].ToString();
                        string gluedPath = Path.Combine(dfysource.getDirPath(), includedPath);
                        SourcePath sp = new SourcePath(gluedPath);
                        outlist.Add(sp);
                        count += 1;
                        match = match.NextMatch();  //- That would be unexpected!
                    }
                    Util.Assert(count <= 1);
                }
            }
            //-Logger.WriteLine(String.Format("{0} includes {1} things", dfysource.getFilesystemPath(), outlist.Count));
            return outlist;
        }
    }
}
