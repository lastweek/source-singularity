// ----------------------------------------------------------------------------
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
// ----------------------------------------------------------------------------

// This program builds all permutations of build variables.


using System;
using System.IO;
using System.Collections.Generic;
using System.Text;
using System.Diagnostics;

namespace BuildAll
{

    class BuildVariable
    {
        public readonly string PropertyName;
        public readonly string[] Values;

        public BuildVariable(string propname, string[] values)
        {
            this.PropertyName = propname;
            this.Values = values;
        }
    }

    static class BuildAll
    {

        static string ProjectPath;

        static string MSBuildPath;

        static readonly BuildVariable[] Variables =
        {
            new BuildVariable("Configuration", new string[] { "Prototype", "Debug", "Release" }),
            new BuildVariable("Platform", new string[] { "ApicPC", "ApicMP", "Apic64" }),
            new BuildVariable("Paging", new string[] { "On", "Off" }),
            new BuildVariable("COLLECTOR_APP", new string[] { "MarkSweep", "Concurrent" }),
            new BuildVariable("COLLECTOR_KERNEL", new string[] { "MarkSweep", "Concurrent" }),
        };

        static void AppendWithPadding(StringBuilder buffer, string value, int total_width)
        {
            buffer.Append(value);
            int padding = total_width - value.Length;
            if (padding > 0)
                buffer.Append(' ', padding);
        }

        static int Main(string[] args)
        {
            ProjectPath = "Distro\\Tiny.proj";


            if (String.IsNullOrEmpty(Environment.GetEnvironmentVariable("SINGULARITY_ROOT"))) {
                Console.Error.WriteLine("Error: The environment variable 'SINGULARITY_ROOT' must be defined, but is not.");
                return 1;
            }


            MSBuildPath = Environment.ExpandEnvironmentVariables(@"%SystemRoot%\Microsoft.Net\Framework\v2.0.50727\msbuild.exe");
            if (!File.Exists(MSBuildPath)) {
                Console.WriteLine("ERROR: Could not find MSBuild.exe");
                return -1;
            }

            int var_count = Variables.Length;

            // 'indexes' is an array of cycle counters, for each variable that we vary over.
            // index of each array slot is an index into Variables array
            // value of each array slot is an index into Variables[i].PropertyValues
            int[] indexes = new int[var_count];
            for (int i = 0; i < indexes.Length; i++)
                indexes[i] = 0; // redundant, of course, but i'm being explicit

            int total_combinations = 1;
            for (int i = 0; i < Variables.Length; i++)
                total_combinations *= Variables[i].Values.Length;
            Console.WriteLine("Total combinations: " + total_combinations);


            Console.WriteLine("Project: " + ProjectPath);


            int[] column_widths = new int[var_count];
            for (int i = 0; i < indexes.Length; i++) {
                column_widths[i] = Variables[i].PropertyName.Length;
                string[] values = Variables[i].Values;
                for (int j = 0; j < values.Length; j++)
                    if (column_widths[i] < values[j].Length)
                        column_widths[i] = values[j].Length;
            }

            StringBuilder line = new StringBuilder();

            // Write table header
            Console.WriteLine();
            line.Length = 0;
            for (int i = 0; i < indexes.Length; i++) {
                AppendWithPadding(line, Variables[i].PropertyName, column_widths[i]);
                line.Append(' ');
            }
            Console.WriteLine(line.ToString());
            line.Length = 0;
            for (int i = 0; i < indexes.Length; i++) {
                line.Append('-', column_widths[i]);
                line.Append(' ');
            }
            Console.WriteLine(line.ToString());

            string[] names = new string[Variables.Length];
            for (int i = 0; i < Variables.Length; i++) {
                names[i] = Variables[i].PropertyName;
            }

            for (;;) {
                bool done;
                for (int i = 0;; i++) {
                    if (i == Variables.Length) {
                        done = true;
                        break;
                    }
                    if (indexes[i] < Variables[i].Values.Length) {
                        done = false;
                        break;
                    }
                }
                if (done) {
                    Console.WriteLine("All variations have been tried.");
                    break;
                }


                line.Length = 0;
                for (int i = 0; i < var_count; i++) {
                    AppendWithPadding(line, Variables[i].Values[indexes[i]], column_widths[i]);
                    line.Append(' ');
                }

                line.Append(" running...");
                Console.Write(line.ToString());

                string[] values = new string[Variables.Length];
                for (int i = 0; i < Variables.Length; i++) {
                    values[i] = Variables[i].Values[indexes[i]];
                }


                bool succeeded;
                TimeSpan time_elapsed;
                RunCombination(names, values, out succeeded, out time_elapsed);

                if (succeeded) {
                    Console.WriteLine(" succeeded  [{0}]", time_elapsed);
                }
                else {
                    Console.WriteLine(" FAILED     [{0}]", time_elapsed);
                }



                // increment indexes, with carry
                done = false;
                for (int i = 0;; i++) {
                    if (i == Variables.Length) {
                        // totally done
                        done = true;
                        break;
                    }

                    indexes[i]++;
                    if (indexes[i] >= Variables[i].Values.Length) {
                        indexes[i] = 0;
                        // implicitly carry
                        if (i == Variables.Length) {
                            // totally done
                            done = true;
                            break;
                        }
                        continue;
                    }
                    else {
                        break;
                    }
                }

                if (done)
                    break;
            }

            Console.WriteLine("done.");

            return 0;
        }


        static void RunCombination(string[] names, string[] values, out bool succeeded, out TimeSpan elapsed)
        {
            StringBuilder buffer = new StringBuilder();
            buffer.Append("/nologo");

            

            for (int i = 0; i < names.Length; i++) {
                buffer.Append(" /p:");
                buffer.Append(names[i]);
                buffer.Append("=");
                buffer.Append(values[i]);
            }

            string log_filename = "msbuild." + String.Join(".", values) + ".log";

            buffer.Append(" /noconsolelogger");
            buffer.Append(" /logger:Microsoft.Build.BuildEngine.FileLogger,Microsoft.Build.Engine;PerformanceSummary;logfile=" + log_filename);

            string cmd = buffer.ToString();

            buffer.Append(" Distro\\Small.proj");
            Debug.WriteLine(cmd);

            ProcessStartInfo info = new ProcessStartInfo();
            info.Arguments = buffer.ToString();
            info.FileName = MSBuildPath;
            info.UseShellExecute = false;

            DateTime time_start = DateTime.Now;

            using (Process p = Process.Start(info)) {
                p.WaitForExit();
                succeeded = (p.ExitCode == 0);
            }

            DateTime time_end = DateTime.Now;

            elapsed = time_end - time_start;
        }
    }


}
