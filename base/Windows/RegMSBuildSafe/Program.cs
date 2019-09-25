// ----------------------------------------------------------------------------
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
// ----------------------------------------------------------------------------

using System;
using System.IO;
using System.Collections.Generic;
using System.Text;
using System.Security.AccessControl;
using Microsoft.Win32;

namespace RegMSBuildSafe
{
    static class Program
    {

        static bool verbose;

        static int Main(string[] args)
        {
            verbose = false;

            if (args.Length == 0) {
                Console.WriteLine("This tool manages registry entries that Visual Studio uses to determine");
                Console.WriteLine("whether a .targets file imported by an MSBuild project is considered 'safe'.");
                Console.WriteLine();
                Console.WriteLine("Use -? for help.");
                return -1;
            }

            try {
                foreach (string arg in args) {
                    if (arg.Length == 0)
                        continue;

                    if (arg[0] == '/' || arg[0] == '-') {
                        string flag = arg.Substring(1).ToLower();

                        if (flag == "i" || flag == "install") {
                            return InstallSafeImports();
                        }
                        else if (flag == "u" || flag == "uninstall") {
                            string prefix = GetSafeImportPrefix();
                            return UninstallSafeImports(prefix);
                        }
                        else if (flag == "us" || flag == "uninstallsing") {
                            return UninstallSafeImports(SafeImportNamePrefix);
                        }
                        else if (flag == "l" || flag == "list") {
                            string prefix = GetSafeImportPrefix();
                            return ListSafeImports(prefix);
                        }
                        else if (flag == "ls" || flag == "listsing") {
                            return ListSafeImports(SafeImportNamePrefix);
                        }
                        else if (flag == "la" || flag == "listall") {
                            return ListSafeImports("");
                        }
                        else if (flag == "v" || flag == "verbose") {
                            verbose = true;
                        }
                        else if (flag == "?" || flag == "help") {
                            Usage();
                            return 0;
                        }
                        else {
                            Usage();
                            return -1;
                        }
                    }
                    else {
                        Usage();
                        return -1;
                    }
                }

                Usage();
                return -1;
            }
            catch (UnauthorizedAccessException ex) {
                ShowException(ex);
                Console.Error.WriteLine("Make sure you are running with Administrator rights, and if necessary,");
                Console.Error.WriteLine("have elevated privileges.");
                return -1;
            }
            catch (Exception ex) {
                ShowException(ex);
                return -1;
            }
        }

        static void ShowException(Exception ex)
        {
            for (Exception focus = ex; focus != null; focus = focus.InnerException) {
                Console.Error.WriteLine("{0}: {1}", ex.GetType().FullName, ex.Message);
            }
        }

        static int InstallSafeImports()
        {
            string prefix = SafeImportNamePrefix;
            string[] targets = GetSingularityTargets();

            using (RegistryKey key = Registry.LocalMachine.OpenSubKey(
                SafeImportsPath, RegistryKeyPermissionCheck.ReadWriteSubTree, RegistryRights.SetValue))
            {
                foreach (string target in targets) {
                    string name = prefix + target;
                    key.SetValue(name, target);

                    if (verbose)
                        Console.WriteLine("Set value: " + name);
                }
            }

            return 0;
        }

        static int UninstallSafeImports(string prefix)
        {
            if (String.IsNullOrEmpty(prefix))
                throw new Exception("The prefix must not be an empty string.");

            if (!prefix.StartsWith(SafeImportNamePrefix, StringComparison.OrdinalIgnoreCase))
                throw new Exception("The prefix can only specify Singularity-related values.");

            using (RegistryKey key = Registry.LocalMachine.OpenSubKey(
                SafeImportsPath, RegistryKeyPermissionCheck.ReadWriteSubTree, RegistryRights.SetValue | RegistryRights.QueryValues))
            {
                string[] names = key.GetValueNames();
                foreach (string name in names) {
                    if (name.StartsWith(prefix, StringComparison.OrdinalIgnoreCase)) {
                        key.DeleteValue(name, false);
                        if (verbose)
                            Console.WriteLine("Deleted value: " + name);
                    }
                }
            }

            return 0;
        }


        /// <summary>
        /// Returns a list of the absolute paths of all of the interesting .targets files
        /// for Singularity.
        /// </summary>
        /// <returns></returns>
        static string[] GetSingularityTargets()
        {
            string root = GetSingularityRoot();

            List<String> alltargets = new List<String>();

            string targets_dir = Path.Combine(root, "Targets");
            string[] targets = Directory.GetFiles(targets_dir, "*.targets", SearchOption.TopDirectoryOnly);
            alltargets.AddRange(targets);

            alltargets.Add(Path.Combine(root, "Paths.targets"));
            alltargets.Add(Path.Combine(root, "Applications\\Paths.targets"));

            return alltargets.ToArray();
        }

        static string GetSafeImportPrefix()
        {
            string singularity_root = GetSingularityRoot();
            return SafeImportNamePrefix + singularity_root;
        }

        static string GetSingularityRoot()
        {
            string singularity_root = Environment.GetEnvironmentVariable("SINGULARITY_ROOT");
            if (String.IsNullOrEmpty(singularity_root))
                throw new Exception("The SINGULARITY_ROOT environment variable is not set.");
            return singularity_root;
        }

        const string SafeImportNamePrefix = "Singularity:";

        static int ListSafeImports(string prefix)
        {
            using (RegistryKey key = Registry.LocalMachine.OpenSubKey(
                SafeImportsPath, RegistryKeyPermissionCheck.ReadWriteSubTree, RegistryRights.QueryValues))
            {
                string[] names = key.GetValueNames();

                foreach (string name in names) {
                    if (!name.StartsWith(prefix, StringComparison.OrdinalIgnoreCase))
                        continue;

                    Console.WriteLine(name);
                }
            }

            return 0;
        }

        static void Usage()
        {
            Console.WriteLine("This tool registers the MSBuild .targets files used by Singularity");
            Console.WriteLine("as 'safe' for use by Visual Studio.  This makes Visual Studio stop");
            Console.WriteLine("complaining about loading projects that import scary .targets files.");
            Console.WriteLine();
            Console.WriteLine("Usage:");
            Console.WriteLine();
            Console.WriteLine("    -v    Turn on verbose output.");
            Console.WriteLine("    -i    Install registry values.");
            Console.WriteLine("    -u    Uninstall registry values for this Singularity tree.");
            Console.WriteLine("    -us   Uninstall registry values for all Singularity trees.");
            Console.WriteLine("    -l    List safe imports for this Singularity tree.");
            Console.WriteLine("    -ls   List safe imports for all Singularity projects.");
            Console.WriteLine("    -la   List safe imports (all of them, not just for Singularity.");
            Console.WriteLine();
            Console.WriteLine("The values are stored in HKEY_LOCAL_MACHINE\\" + SafeImportsPath + ".");
            Console.WriteLine("The environment variable SINGULARITY_ROOT must be set, so that the");
            Console.WriteLine("tool can locate the .targets files.  All targets files found in the");
            Console.WriteLine("%SINGULARITY_ROOT%\\Targets directory will be added to the registry.");
        }

        const string SafeImportsPath = @"Software\Microsoft\VisualStudio\8.0\MSBuild\SafeImports";
    }
}
