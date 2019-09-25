using System;
using System.Collections;
using System.IO;
using System.Reflection;

public class driver {
    public static string progname = "csic";
    static string oname = null;
    static Compiler compiler;
    static ArrayList inputs = new ArrayList();

    public static int Main(string[] argv) {
        IImportReader reader = new BartokReader();
        int nopts = 0;
        compiler = new Compiler(reader, Console.Out);
        compiler.AddVisitor(new VisitorDelegate(csi_bind.visit));
        compiler.AddVisitor(new VisitorDelegate(csi_typecheck.visit));
        compiler.AddVisitor(new VisitorDelegate(csi_ilgen.visit));

        argv = ProcessResponseFiles(argv);
        if (argv == null) {
            return 1;
        }
        
        for (int i = 0; i < argv.Length; i++) {
            string arg = argv[i];
            if (arg[0] == '-' || (arg[0] == '/' && arg[1] != '/'))
                option(arg.Substring(1), ref nopts);
            else
                inputs.Add(arg);
        }

        if (inputs.Count == 0 && nopts > 0)
            compiler.Compile(Console.In, Console.Out, argv);
        else if (inputs.Count > 0 && oname != null)
            compiler.Compile((string[])inputs.ToArray(typeof (string)), oname, argv);
        else if (inputs.Count > 0)
            compiler.Compile((string[])inputs.ToArray(typeof (string)), argv);
        return compiler.Msg.Count;
    }

    private static string[] ProcessResponseFiles(string[] argv)
    {
        ArrayList results = new ArrayList();
        foreach (string arg in argv) {
            if (arg[0] == '@') {
                string filename = arg.Substring(1);
                try {
                    string[] responseFileContents = File.ReadAllLines(filename);
                    results.AddRange(responseFileContents);
                    
                } catch (Exception e) {
                    Console.WriteLine("error: can't read response file '{0}': '{1}'", filename, e.Message);
                    return null;
                }
            } else {
                results.Add(arg);
            }
        }
        return (string[]) results.ToArray(typeof(string));
    }

    static void help() {
        Console.WriteLine("{0} [ option... ] [ file... ]", progname);
        Console.WriteLine(
@"-help -?    display this text
-lib:dirs   look for assemblies in dirs, a comma-separated list
-out:file   emit the output into file (default is standard output)
-outdir:dir emit temporary files into dir
-r[eference]:files
            load metadata from the assembly in files
-t[arget]:library -t[arget]:exe -t[arget]:winexe
            build a library, console executable, or windows executable
            (default is console executable)
-nostdlib   omit standard library
-unsafe     permit unsafe code
-ilasm:file ilasm command
@file       read options from file");
    }

    static void initLibrary(Compiler compiler) {
        Microsoft.Win32.RegistryKey rk = Microsoft.Win32.Registry.LocalMachine.OpenSubKey("SOFTWARE\\Microsoft\\.NETFramework");
        if (rk != null) {
            string InstallRoot = (string)rk.GetValue("InstallRoot");
            string Version = (string)rk.GetValue("Version");
            if (InstallRoot != null) {
                if (Version == null)
                    foreach (string dir in Directory.GetDirectories(InstallRoot, "v*"))
                        if (File.Exists(dir + "\\mscorlib.dll")) {
                            Version = Path.GetFileName(dir);
                            break;
                        }
                if (!InstallRoot.EndsWith("\\"))
                    InstallRoot += "\\";
            }
            if (InstallRoot != null && Version != null)
                compiler.AddLibraryPath(InstallRoot + Version);
        }
    }
    static bool option(string arg, ref int nopts) {
        string arg0 = null;
        int i;
        nopts++;
        if ((i = arg.IndexOf(':')) >= 0)
            arg0 = arg.Substring(i + 1);
        if (arg == "help" || arg == "?") {
            help();
            nopts--;
        } else if (arg.StartsWith("out:"))
            oname = arg0;
        else if (arg.StartsWith("r:") || arg.StartsWith("reference:")) {
            foreach (string f in arg0.Split(','))
                if (!compiler.AddReference(f.Split('=')[0]))
                    compiler.Msg.WriteLine("{0}: can't find \"{1}\"", progname, f);
        } else if (arg.StartsWith("lib:")) {
            for ( ; (i = arg0.IndexOf(',')) >= 0; arg0 = arg0.Substring(i + 1))
                compiler.AddLibraryPath(arg0.Substring(0, i));
            compiler.AddLibraryPath(arg0);
        } else
            return false;
        return true;
    }
}
