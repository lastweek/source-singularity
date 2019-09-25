// ----------------------------------------------------------------------------
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
// ----------------------------------------------------------------------------

using System;
using System.IO;
namespace mkpxecom
{
	/// <summary>
	/// Summary description for mkpxecom.
	/// </summary>
    public class mkpxecom
    {
        static void Main(string[] args)
        {
            if (args.Length != 2) {
                Console.WriteLine("Incorrect usage");
                return;
            }
        int size = Convert.ToInt32(args[0]);
            string fileName = args[1];
            if (!File.Exists(fileName)) {
                FileStream fs = new FileStream(fileName, FileMode.Create);
                byte[] buffer = new byte[size];
                fs.Write(buffer, 0, size);
            }
            else {
                FileStream fs = new FileStream(fileName, FileMode.Open);
                if (fs.Length != size) {
                    throw new Exception("File is of wrong size");
                }
            }
            
        }
    }
}
