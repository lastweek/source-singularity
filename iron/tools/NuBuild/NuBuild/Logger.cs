using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Threading.Tasks;
using System.IO;

namespace NuBuild
{
    class Logger
    {
        private static StreamWriter sw;
        private static void open()
        {
            if (sw == null)
            {
                sw = new StreamWriter("nubuild.log");
            }
        }
        public static void Write(string m)
        {
            open();
            sw.Write(m);
            sw.Flush();
            System.Console.Write(m);
        }
        public static void WriteLine(string m)
        {
            Write(m + System.Environment.NewLine);
        }
    }
}
