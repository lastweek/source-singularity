// ----------------------------------------------------------------------------
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
// ----------------------------------------------------------------------------

using System;
using System.IO;
using System.Collections.Generic;
using System.Text;
using System.Xml;

namespace CheckProject
{
    static class Program
    {
        static int Main(string[] args)
        {
            _name_table = new NameTable();
            _namespace_manager = new XmlNamespaceManager(_name_table);
            _namespace_manager.AddNamespace("", MSBuildNamespace);
            _namespace_manager.AddNamespace("msbuild", MSBuildNamespace);

            int projects_checked_count = 0;

            int failed_project_count = 0;

            foreach (string arg in args) {
                if (arg.StartsWith("-") || arg.StartsWith("/")) {
                    string option = arg.Substring(1);

                    switch (option) {
                        case "fix":
                            _fix_enabled = true;
                            break;

                        case "fake":
                            _fake_fix = true;
                            _fix_enabled = true;
                            break;

                        default:
                            Console.WriteLine("Error: Invalid command-line parameter: " + option);
                            return 1;
                    }
                }
                else {
                    projects_checked_count++;

                    try {
                        ProjectChecker checker = new ProjectChecker();
                        bool result = checker.CheckProjectFile(arg);
                        if (!result) {
                            Console.WriteLine("Error: Project '{0}' failed validation.", arg);
                            failed_project_count++;
                        }
                    }
                    catch (Exception ex) {
                        Console.WriteLine("An exception occurred while processing project '{0}'.", arg);
                        ShowException(ex);
                    }
                }
            }

            if (failed_project_count > 0) {
                Console.WriteLine("{0} project(s) failed validation.", failed_project_count);
                return 1;
            }

            if (projects_checked_count == 0) {
                Usage();
                return 1;
            }

            Console.WriteLine("All projects checked are ok.");
            return 0;
        }

        static void Usage()
        {
            Console.WriteLine("This tool checks Singularity project files.");
            Console.WriteLine("Usage: chkproj [-fix] [-fake] [project1.csproj] ... [projectN.csproj]");
            Console.WriteLine();
            Console.WriteLine("    -fix     Make changes to the project to fix warnings, and write changes to file.");
            Console.WriteLine("    -fake    Make changes, display the changed project, but do not write file.");


        }

        /// <summary>
        /// If true, then make changes to the project file that would fix the warnings.
        /// </summary>
        static bool _fix_enabled;

        /// <summary>
        /// If true, then don't actually write the file.
        /// </summary>
        static bool _fake_fix;

        class ProjectChecker
        {
            string _project_file;

            void WriteLine(string line)
            {
                Console.WriteLine("{0} : {1}", _project_file, line);
            }

            void WriteLine(string format, params object[] args)
            {
                WriteLine(String.Format(format, args));
            }

            public bool CheckProjectFile(string project_file)
            {
                _project_file = project_file;

                WriteLine("Checking project...");

                XmlDocument document = new XmlDocument();
                document.PreserveWhitespace = true;
                try {
                    document.Load(project_file);
                }
                catch (Exception ex) {
                    WriteLine("An error occurred while loading project '{0}'.", project_file);
                    ShowException(ex);
                    return false;
                }

                if (document.DocumentElement.Name != "Project") {
                    Console.WriteLine("Error: File does not appear to be an MSBuild project.");
                    return false;
                }


                XmlNodeList import_nodes = document.SelectNodes("/msbuild:Project/msbuild:Import", _namespace_manager);
                WriteLine("Imports: ({0})", import_nodes.Count);
                foreach (XmlNode node in import_nodes) {
                    WriteLine("    " + node.OuterXml);
                }

                bool has_global_targets_import = false;
                bool has_old_global_import = false;
                XmlElement old_global_import_element = null;

                foreach (XmlNode import_node in import_nodes) {
                    XmlElement import_element = (XmlElement)import_node;
                    string import_path = import_element.GetAttribute("Project");
                    if (String.IsNullOrEmpty(import_path)) {
                        WriteLine("Warning: Project contains an <Import> element that does not have a 'Project' attribute.");
                    }

                    if (String.Compare(import_path, GlobalTargetsImport, StringComparison.OrdinalIgnoreCase) == 0) {
                        has_global_targets_import = true;
                    }

                    if (String.Compare(Path.GetFileName(import_path), "Paths.targets", StringComparison.OrdinalIgnoreCase) == 0) {
                        has_old_global_import = true;
                        old_global_import_element = import_element;
                        WriteLine("Error: Project contains an <Import> of the old Paths.targets file.");
                    }

                    if (import_path.StartsWith("$(MSBuildBinPath)", StringComparison.OrdinalIgnoreCase)) {
                        WriteLine("This project appears to use the CLR build targets; it is not a Singularity project.");
                        WriteLine("To remove this error, remove all <Import> elements that refer to $(MSBuildBinPath) targets.");
                        return false;
                    }
                }

                if (!has_global_targets_import) {
                    WriteLine("Warning: This project does not have an <Import> directive for " + GlobalTargetsImport + ".");
                }



                // Now fix problems, if we're allowed to.

                if (_fix_enabled) {
                    if (!has_global_targets_import) {
                        WriteLine("Fixing: Adding <Import> directive for " + GlobalTargetsImport + ".");
                        XmlElement element = document.CreateElement("Import", MSBuildNamespace);
                        element.SetAttribute("Project", GlobalTargetsImport);
                        document.DocumentElement.InsertAfter(element, null);
                    }

                    if (has_old_global_import) {
                        WriteLine("Fixing: Removing old <Import> directive for '{0}'",
                            old_global_import_element.GetAttribute("Project"));
                        document.DocumentElement.RemoveChild(old_global_import_element);
                    }

                    if (_fake_fix) {
                        WriteLine("New project:");
                        XmlTextWriter writer = new XmlTextWriter(Console.Out);
                        writer.Formatting = Formatting.Indented;
                        document.WriteTo(writer);
                    }
                    else {
                        string new_project_path = Path.GetTempFileName();
                        WriteLine("Writing new project file: " + new_project_path);
                        try {
                            using (FileStream new_project_stream = File.Open(new_project_path, FileMode.Create, FileAccess.Write, FileShare.None))
                            using (XmlTextWriter writer = new XmlTextWriter(new_project_stream, Encoding.UTF8))
                            {
                                writer.Formatting = Formatting.Indented;
                                document.WriteTo(writer);
                            }
                            WriteLine("Replacing...");
                            File.Replace(new_project_path, project_file, null);
                            WriteLine("Done.");
                        }
                        finally {
                            try {
                                File.Delete(new_project_path);
                            }
                            catch (IOException) {
                            }
                        }
                    }

                }

                return true;

            }
        }

        const string GlobalTargetsImport = "$(SINGULARITY_GLOBAL_TARGETS)";

        static XmlNamespaceManager _namespace_manager;
        static NameTable _name_table;

        const string MSBuildNamespace = "http://schemas.microsoft.com/developer/msbuild/2003";

        static void ShowException(Exception chain)
        {
            for (Exception ex = chain; ex != null; ex = ex.InnerException) {
                Console.WriteLine("{0}: {1}", ex.GetType().FullName, ex.Message);
            }
        }
    }
}
