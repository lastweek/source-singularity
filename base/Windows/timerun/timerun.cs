// ----------------------------------------------------------------------------
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
// ----------------------------------------------------------------------------

using System;
using System.Diagnostics;
using System.Text;
using Windows;

namespace timerun
{
    class timerun
    {
        static int Main(string[] args)
        {
            try {
                if (args.Length < 1) {
                    Usage();
                    return 1;
                }

                string program = args[0];
                string arguments = String.Join(" ", args, 1, args.Length - 1);

                IntPtr job_handle = Kernel32.CreateJobObject();
                if (job_handle == IntPtr.Zero) {
                    WriteLine("WARNING: Failed to create job object; cannot gather CPU usage info.");
                }

                using (Process process = new Process()) {
                    process.StartInfo.UseShellExecute = false;
                    process.StartInfo.Arguments = arguments;
                    process.StartInfo.FileName = program;

                    DateTime timeStarted = DateTime.Now;

                    process.Start();

                    if (job_handle != IntPtr.Zero) {
                        if (!Kernel32.AssignProcessToJobObject(job_handle, process.Handle)) {
                            WriteLine("WARNING: Failed to assign child process to job.");
                            WriteLine("The process may have already terminated.");
                        }
                    }

                    process.WaitForExit();

                    DateTime timeEnded = DateTime.Now;

                    TimeSpan elapsed = timeEnded - timeStarted;

                    const string times_format = " {0,-32} : {1}";

                    if (job_handle != IntPtr.Zero) {
                        try {
                            JOBOBJECT_BASIC_ACCOUNTING_INFORMATION job_info;
                            job_info = Kernel32.QueryJobObjectBasicAccountingInformation(job_handle);

                            TimeSpan total_job_time = job_info.TotalUserTime + job_info.TotalKernelTime;

                            WriteLine(
                                times_format,
                                "CPU time consumed by jobs",
                                total_job_time);

                            WriteLine(
                                times_format,
                                "    in user mode",
                                job_info.TotalUserTime);

                            WriteLine(
                                times_format,
                                "    in kernel mode",
                                job_info.TotalKernelTime);

                            WriteLine(
                                times_format,
                                "Elapsed time (wall time)",
                                elapsed);

                            WriteLine("");
                            if (elapsed.TotalMilliseconds > 0) {
                                double elapsed_ms = elapsed.TotalMilliseconds;
                                double total_job_ms = total_job_time.TotalMilliseconds;
                                double throughput_ratio = total_job_ms / elapsed_ms;
                                double throughput_percent = Math.Round(throughput_ratio * 100.0);
                                WriteLine("      Parallel throughput ratio: {0}%", throughput_percent);
                            }
                            else {
                                WriteLine("      Too little time elapsed to compute ratio.");
                            }
                        }
                        catch (Exception ex) {
                            WriteLine("FAILED to query job info!");
                            ShowException(ex);
                        }
                    }
                    else {
                        WriteLine(" Child process times not available.");
                    }

                    return process.ExitCode;
                }
            }
            catch (Exception ex) {
                ShowException(ex);
                return 1;
            }
        }

        static void WriteLine(string line)
        {
            Console.WriteLine(Prefix + line);
        }

        static void WriteLine(string format, params object[] args)
        {
            WriteLine(String.Format(format, args));
        }

        const string Prefix = "TIMERUN: ";

        static void Usage()
        {
            Console.WriteLine("Usage: TIMERUN program args ...");
            Console.WriteLine();
            Console.WriteLine("    TIMERUN runs a program, then displays CPU usage information for the program");
            Console.WriteLine("    and all of its child processes.");
        }

        static void ShowException(Exception chain)
        {
            for (Exception ex = chain; ex != null; ex = ex.InnerException) {
                Console.WriteLine(ex.GetType().FullName + ": " + ex.Message);
            }
        }


    }
}
