using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Threading.Tasks;
using System.Diagnostics;
using System.IO;

namespace NuBuild
{
    class ProcessInvoker
    {
        public Disposition disposition;
        public double cpuTime;
        public int exitCode;
        public StreamWriter stdoutFile;
        public StringBuilder stdout;
        public StringBuilder stderr;
        RcHandling rcHandling;
        string _tmpStdoutPath;

        const bool alwaysEmitDiagnostics = true;

        public enum RcHandling {
            NONZERO_RC_IS_FAILURE,
            NONZERO_RC_IS_OKAY
        }

        public ProcessInvoker(
            string executable,
            string[] args,
            RcHandling rcHandling,
            BuildObject failureBase,
            string finalStdoutPath = null,
            string dbgText = null,
            bool allowAbsoluteExe = false,
            bool allowAbsoluteArgs = false,
            string workingDir = null)
        {
            Util.Assert(allowAbsoluteExe || !executable.Contains(":"));  //- Hey, this looks like an absolute path! Use .getRelativePath() to tolerate crossing machine boundaries.
            foreach (string arg in args)
            {
                //- Pardon my distasteful heuristic to avoid flagging /flag:value args.
                Util.Assert(allowAbsoluteArgs || arg.Length < 2 || arg[1] != ':');  //- Hey, this looks like an absolute path! Use .getRelativePath() to tolerate crossing machine boundaries.
            }

            this.rcHandling = rcHandling;
            stdout = new StringBuilder();
            stderr = new StringBuilder();

            using (Job job = new Job())
            {
                using (Process proc = new Process())
                {
                    proc.StartInfo.FileName = Path.Combine(BuildEngine.theEngine.getIronRoot(), executable);
                    //- TODO Is there a better way to escape the args to avoid problems with spaces?
                    proc.StartInfo.Arguments = String.Join(" ", args);

                    proc.StartInfo.WorkingDirectory = workingDir == null ? BuildEngine.theEngine.getIronRoot() : workingDir;
                    proc.StartInfo.RedirectStandardOutput = true;
                    if (finalStdoutPath != null)
                    {
                        _tmpStdoutPath = finalStdoutPath + ".tmp";
                        stdoutFile = new StreamWriter(_tmpStdoutPath);
                        proc.OutputDataReceived += new DataReceivedEventHandler(stdoutRedirectHandler);
                    }
                    else
                    {
                        //- collect stdout here for diagnostics.
                        proc.OutputDataReceived += new DataReceivedEventHandler(stdoutHandler);
                    }
                    proc.StartInfo.RedirectStandardError = true;
                    proc.ErrorDataReceived += new DataReceivedEventHandler(stderrHandler);
                    proc.StartInfo.UseShellExecute = false;

                    string commandLine = proc.StartInfo.FileName + " " + proc.StartInfo.Arguments;
                    if (alwaysEmitDiagnostics)
                    {
                        //- In diagnostic mode, we emit the command line twice, once ahead in case Boogie decides
                        //- to run away and never come back.
                        BuildObject failureBatObj = failureBase.makeOutputObject(".bat");
                        failureBatObj.prepareObjDirectory();
                        File.WriteAllText(failureBatObj.getFilesystemPath(), commandLine);
                    }

                    proc.Start();
                    job.AddProcess(proc);
                    proc.BeginOutputReadLine();
                    proc.BeginErrorReadLine();
                    proc.WaitForExit();

                    cpuTime = job.GetCpuTime().TotalSeconds;

                    exitCode = proc.ExitCode;
                    if (stdoutFile != null)
                    {
                        stdoutFile.Close();
                    }

                    if (passed())
                    {
                        disposition = new Fresh();
                    }
                    else
                    {
                        //- sheesh. Some tools emit error messages to stdout.
                        Failed f = new Failed(getStdoutString() + stderr.ToString());
                        f.AddError("Command line: " + commandLine + "\n");
                        disposition = f;
                    }

#pragma warning disable 429 //- alwaysEmitDiagnostics is a compile-time constant that can hide expression !passed()
                    if (failureBase != null && (alwaysEmitDiagnostics || !passed()))
#pragma warning restore 429
                    {
                        failureBase.prepareObjDirectory();
                        File.WriteAllText(failureBase.makeOutputObject(".bat").getFilesystemPath(), commandLine);
                        File.WriteAllText(failureBase.makeOutputObject(".txt").getFilesystemPath(), dbgText);
                        File.WriteAllText(failureBase.makeOutputObject(".stdout").getFilesystemPath(), getStdoutString());
                        File.WriteAllText(failureBase.makeOutputObject(".stderr").getFilesystemPath(), getStderr());
                    }
                }
            }

            if (passed() && _tmpStdoutPath!=null)
            {
                File.Delete(finalStdoutPath);
                File.Move(_tmpStdoutPath, finalStdoutPath);
                _tmpStdoutPath = null;
            }
        }

        string getStdoutString()
        {
            if (_tmpStdoutPath != null)
            {
                return File.ReadAllText(_tmpStdoutPath);
            }
            else
            {
                return getStdout();
            }
        }

        void stdoutRedirectHandler(object sendingProcess, DataReceivedEventArgs dataLine)
        {
            stdoutFile.WriteLine(dataLine.Data);
        }
        void stdoutHandler(object sendingProcess, DataReceivedEventArgs dataLine)
        {
            stdout.Append(dataLine.Data + "\n");
        }
        void stderrHandler(object sendingProcess, DataReceivedEventArgs dataLine)
        {
            stderr.Append(dataLine.Data + "\n");
        }
        public string getStdout() { return stdout.ToString(); }
        public string getStderr() { return stderr.ToString(); }

        public bool passed()
        {
            return rcHandling==RcHandling.NONZERO_RC_IS_OKAY || exitCode == 0;
        }
    }
}
