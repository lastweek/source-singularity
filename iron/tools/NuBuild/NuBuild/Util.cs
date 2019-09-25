using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Threading.Tasks;
using System.IO;
using System.Security.Cryptography;
using System.Runtime.Remoting.Metadata.W3cXsd2001;
using System.Diagnostics;
using System.Threading;

namespace NuBuild
{
    class Util
    {
        public static string hashString(string input)
        {
            byte[] buffer = new byte[input.Length * sizeof(char)];
            System.Buffer.BlockCopy(input.ToCharArray(), 0, buffer, 0, buffer.Length);
            SHA256Managed hasher = new SHA256Managed();
            byte[] rawHash = hasher.ComputeHash(buffer);
            return new SoapHexBinary(rawHash).ToString();
        }

        public static string hashFilesystemPath(string filesystemPath)
        {
            //-Logger.WriteLine("Hashing " + filesystemPath);
            using (FileStream stream = File.OpenRead(filesystemPath))
            {
                SHA256 sha = new SHA256Managed();
                byte[] rawHash = sha.ComputeHash(stream);
                string rc = new SoapHexBinary(rawHash).ToString();
                //-Logger.WriteLine("fresh hash of " + obj.getFilesystemPath() + " yields " + rc);
                return rc;
            }
        }

        //- win32 MAX_PATH is 260 according to Internets
        const int MAX_MUNGED_LENGTH = 150;
        
        public static string mungeClean(string s)
        {
            StringBuilder sb = new StringBuilder();
            bool lastIsLetter = false;
            foreach (char c in s)
            {
                if (char.IsLetter(c) || char.IsNumber(c))
                {
                    sb.Append(c);
                    lastIsLetter = true;
                }
                else
                {
                    if (lastIsLetter)
                    {
                        sb.Append('-');
                    }
                    lastIsLetter = false;
                }
            }

            if (sb.Length > MAX_MUNGED_LENGTH)
            {
                string originalPathHash = Util.hashString(sb.ToString());
                int additionsLength = originalPathHash.Length + 3;
                sb.Remove(MAX_MUNGED_LENGTH-additionsLength, sb.Length-(MAX_MUNGED_LENGTH-additionsLength));
                sb.Append("...");
                sb.Append(originalPathHash);
            }

            return sb.ToString();
        }

        //- replace characters in a filename the same way DafnySpec/DafnyCC does.
        public static string dafnySpecMungeName(string s)
        {
            return s.Replace('.', '_').Replace('-', '_');
        }

        //- returns null if s doesn't end with eold.
        public static string replaceExtension(string s, string eold, string enew)
        {
            if (s.EndsWith(eold))
            {
                return s.Substring(0, s.Length - eold.Length) + enew;
            }
            else
            {
                return null;
            }
        }

        public static void Assert(bool condition)
        {
            if (!condition)
            {
                Logger.WriteLine("Assert failure.");
                Debug.Assert(condition);
                while (true)
                {
                    Logger.WriteLine("Something broke in assert");
                    Debugger.Break();
                    Thread.Sleep(10000);
                }
            }
        }
    }
}
