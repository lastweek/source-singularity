using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Threading.Tasks;
using System.IO;

namespace NuBuild
{
    class DbgHashSpeedTest
    {
        public static void thing()
        {
            Directory.SetCurrentDirectory("c:\\users\\howell\\verve2\\iron");
            string[] theFiles = File.ReadAllLines("hashlist");
            Logger.WriteLine("I found " + theFiles.Count() + " files");

            foreach (string file in theFiles)
            {
                string s = Util.hashFilesystemPath(file);
                Logger.WriteLine(s);
            }
        }
    }
}
