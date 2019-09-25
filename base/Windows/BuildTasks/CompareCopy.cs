// ----------------------------------------------------------------------------
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
// ----------------------------------------------------------------------------

using System;
using System.IO;
using Microsoft.Build.Framework;
using Microsoft.Build.Utilities;
using System.Collections;

namespace Microsoft.Singularity.BuildTasks
{
    public class CompareCopy : ExecTaskBase
    {
        private ITaskItem[] copiedFiles;
        private ITaskItem[] destinationFiles;
        private ITaskItem   destinationFolder;
        private ITaskItem[] sourceFiles;

        protected override bool Execute()
        {
            if (this.sourceFiles == null || this.sourceFiles.Length == 0) {
                this.destinationFiles = new TaskItem[0];
                this.copiedFiles = new TaskItem[0];
                return true;
            }

            if (!this.InputsValid() || !this.InitializeDestinationFiles()) {
                return false;
            }

            return MakeCopies();
        }

        private void LogError(string format, params Object[] args)
        {
            base.LogError(string.Format(format, args));
        }

        private bool InputsValid()
        {
            if (IsNullOrEmpty(this.destinationFiles) ||
                null == this.destinationFolder) {
                LogError("No destination files were specified.");
                return false;
            }
            else if (null != this.destinationFolder &&
                     null != this.destinationFiles) {
                LogError("Specify DestinationFolder OR DestinationFiles.");
                return false;
            }
            else if (null != this.destinationFiles &&
                     this.sourceFiles.Length != this.destinationFiles.Length) {
                LogError("Number of SourceFiles and DestinationFiles differs.");
                return false;
            }

            return true;
        }

        /// <summary>
        /// Initializes the destinationFiles member in preparation if not
        /// specified by the user.
        /// </summary>
        /// <returns>true on success, false if a failure composing names 
        /// occurs.</returns>
        private bool InitializeDestinationFiles()
        {
            if (this.destinationFiles != null) {
                return true;
            }

            this.destinationFiles = new ITaskItem [this.sourceFiles.Length];

            string directory = this.destinationFolder.ItemSpec;

            for (int i = 0; i < this.sourceFiles.Length; i++) {
                string destination;

                try {
                    string file = Path.GetFileName(
                        this.sourceFiles[i].ItemSpec
                        );
                    destination = Path.Combine(directory, file);
                }
                catch (System.ArgumentException) {
                    LogError(
                        "Failed making destination file name for \"{0}\"",
                            this.sourceFiles[i].ItemSpec
                        );
                    this.destinationFiles = new ITaskItem [0];
                    return false;
                }

                this.destinationFiles[i] = new TaskItem(destination);
                this.sourceFiles[i].CopyMetadataTo(this.destinationFiles[i]);
            }

            return true;
        }

        /// <summary>
        /// Walks lists of source and destination files and performs 
        /// copies if files differ.
        /// </summary>
        /// <returns>true on success, false if an exception 
        /// stopped processing.</returns>
        private bool MakeCopies()
        {
            ArrayList copied = new ArrayList();

            bool success = true;
            for (int i = 0; i < this.sourceFiles.Length; i++) {
                if (this.CopyIfNecessary(this.sourceFiles[i].ItemSpec,
                                         this.destinationFiles[i].ItemSpec)) {
                    copied.Add(this.destinationFiles[i]);
                }
                else {
                    success = false;
                    break;
                }
            }

            this.copiedFiles = (ITaskItem[])copied.ToArray(typeof(ITaskItem));
            return success;
        }

        /// <summary>
        /// Copies source file to destination if the destination does 
        /// not exist or the source file differs from the destination.
        /// </summary>
        /// <param name="source">source file name</param>
        /// <param name="destination">destination file name</param>
        /// <returns>true on success, false if an exception occurred during 
        /// checking or copy.</returns>
        private bool CopyIfNecessary(string source, string destination)
        {
            try {
                if (File.Exists(source) == false) {
                    LogError("Source file does not exist: \"{0}\".", source);
                    return false;
                }
                if (File.Exists(destination) == false ||
                    FileContentsDiffer(source, destination)) {
                    File.Copy(source, destination);
                }
                return true;
            }
            catch (Exception e) {
                LogError("Exception raised: {0}.", e);
                return false;
            }
        }

        /// <summary>
        /// Compares source and destination file contents.
        /// </summary>
        /// <param name="source">source file name</param>
        /// <param name="destination">destination file name</param>
        /// <returns>true if file contents differ, false if the same</returns>
        private static bool FileContentsDiffer(string source,
                                               string destination)
        {
            FileInfo fis = new FileInfo(source);
            FileInfo fid = new FileInfo(destination);

            if (fis.Length != fid.Length) {
                return true;
            }

            int bs, bd;
            using (Stream ss = fis.OpenRead()) {
                using (Stream sd = fid.OpenRead()) {
                    do {
                        bs = ss.ReadByte();
                        bd = sd.ReadByte();
                    } while ((bs == bd) && (bs != -1));
                }
            }

            return bs != bd;
        }

        private static bool IsNullOrEmpty(ITaskItem[] x)
        {
            return null == x || 0 == x.Length;
        }

        // --------------------------------------------------------------------
        // Properties

        public ITaskItem[] CopiedFiles
        {
            get { return this.copiedFiles; }
            set { this.copiedFiles = value; }
        }

        public ITaskItem[] DestinationFiles
        {
            get { return this.destinationFiles; }
            set { this.destinationFiles = value; }
        }

        public ITaskItem DestinationFolder
        {
            get { return this.destinationFolder; }
            set { this.destinationFolder = value; }
        }

        public ITaskItem[] SourceFiles
        {
            get { return this.sourceFiles; }
            set { this.sourceFiles = value; }
        }
    }
}
