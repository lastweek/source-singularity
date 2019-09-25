using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Threading.Tasks;
using System.IO;

namespace NuBuild
{
    class DbgFileCopySpeedTest
    {
        public static void thing()
        {
            Directory.SetCurrentDirectory("c:\\users\\howell\\verve2\\iron");
            Directory.CreateDirectory("dummy");
            Directory.CreateDirectory("dummy/Results");
            Directory.CreateDirectory("dummy/Objects");
            Directory.CreateDirectory("dummy/Sources");
            foreach (string path in Directory.EnumerateFiles("nucache", "*", SearchOption.AllDirectories))
            {
                string fn = path.Substring(path.IndexOf("nucache")+8);
                string source = Path.Combine("nucache", fn);
                string dest = Path.Combine("dummy", fn);
                //-Logger.WriteLine("Copy " + source + " to " + dest);
                //-File.Copy(source, dest);

                File.Delete(dest);
                using (FileStream outStream = File.OpenWrite(dest))
                {
                    bool dummy = File.Exists(source);
                    using (Stream inStream = File.OpenRead(source))
                    {
                        inStream.CopyTo(outStream);
                    }
                }

            }
        }
    }
}
