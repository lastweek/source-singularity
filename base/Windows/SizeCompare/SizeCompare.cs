using System;
using System.IO;

// SizeCompare compares the sizes of two files.  Returns whether they are equal (0).

class SizeCompare
{
    static int Main(string[] args)
    {
        if (args == null || args.Length != 2) {
            Console.WriteLine("Usage: SizeCompare <file1> <file2>");
            return 0;
        }

        FileInfo fi1 = new FileInfo(args[0]);
        if (!fi1.Exists) {
            Console.WriteLine("{0} does not exist", args[0]);
            return 0;
        }

        FileInfo fi2 = new FileInfo(args[1]);
        if (!fi2.Exists) {
            Console.WriteLine("{0} does not exist", args[1]);
            return 0;
        }

        if (fi1.Length == fi2.Length) {
            Console.WriteLine("{0} and {1} are the same size", args[0], args[1]);
            return 0;
        }

        Console.WriteLine("{0} and {1} are different sizes", args[0], args[1]);
        return -1;
    }
}
