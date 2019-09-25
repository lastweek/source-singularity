// ----------------------------------------------------------------------------
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
// ----------------------------------------------------------------------------

using System;
using System.IO;
using System.Collections.Generic;
using System.Text;
using Microsoft.Build.Framework;

namespace Microsoft.Singularity.BuildTasks
{
    public class Csic : ExecTaskBase
    {
        protected override bool Execute()
        {
            if (_sources == null || _sources.Length == 0) {
                LogError("No source files were specified.");
                return false;
            }

            List<String> args = new List<String>();

            args.Add("/nologo");


            if (String.IsNullOrEmpty(_outputAssembly)) {
                LogError("The 'OutputAssembly' parameter is required, but no value was provided.");
                return false;
            }

            args.Add("/out:" + _outputAssembly);

            string outputAssemblyDir = Path.GetDirectoryName(_outputAssembly);
            string outputAssemblyBaseName = Path.GetFileNameWithoutExtension(_outputAssembly);
            string outputSymbolsPath = Path.Combine(outputAssemblyDir, outputAssemblyBaseName + ".pdb");


            if (!String.IsNullOrEmpty(_outputDir))
                args.Add("/outdir:" + _outputDir);

            string targetType = _targetType;
            if (String.IsNullOrEmpty(targetType)) {
                LogError("The 'TargetType' property is required, but no value was provided.");
                return false;
            }

            targetType = targetType.ToLower();
            if (targetType != "exe" && targetType != "library" && targetType != "winexe") {
                LogError(String.Format("The value '{0}' is valid for the 'TargetType' property.", targetType));
                return false;
            }

            args.Add("/t:" + targetType);

            if (_allowUnsafeBlocks)
                args.Add("/unsafe");

            if (_noStdlib)
                args.Add("/nostdlib");


            if (_references != null) {
                foreach (ITaskItem reference in _references) {
                    string arg = "/r:" + reference.ItemSpec;

                    string alias = reference.GetMetadata("Alias");
                    if (!String.IsNullOrEmpty(alias)) {
                        arg += "=" + alias;
                    }
                    args.Add(arg);
                }
            }

            foreach (ITaskItem source in _sources) {
                args.Add(source.ItemSpec);
            }

            bool result = ExecuteProgram(ExecutablePath, args);

            if (!result) {
                // CSIC has a bug; if it encounters an error while building an assembly, it will
                // not delete the half-baked output.  So we manually clean up after it.

                Util.DeleteFileIgnoreErrors(_outputAssembly);
                Util.DeleteFileIgnoreErrors(outputSymbolsPath);
            }

            return result;
        }

        ITaskItem[] _references;

        public ITaskItem[] References
        {
            get { return _references; }
            set { _references = value; }
        }

        ITaskItem[] _sources;

        public ITaskItem[] Sources
        {
            get { return _sources; }
            set { _sources = value; }
        }

        bool _allowUnsafeBlocks;

        public bool AllowUnsafeBlocks
        {
            get { return _allowUnsafeBlocks; }
            set { _allowUnsafeBlocks = value; }
        }

        bool _isKey;

        public bool IsKey
        {
            get { return _isKey; }
            set { _isKey = value; }
        }

        string _outputAssembly;
        public string OutputAssembly
        {
            get { return _outputAssembly; }
            set { _outputAssembly = value; }
        }

        string _outputDir;
        public string OutputDir
        {
            get { return _outputDir; }
            set { _outputDir = value; }
        }

        string _executablePath = "csic.exe";
        public string ExecutablePath
        {
            get { return _executablePath; }
            set { _executablePath = value; }
        }

        bool _noStdlib;
        public bool NoStandardLib
        {
            get { return _noStdlib; }
            set { _noStdlib = value; }
        }

        string _targetType = "Exe";

        public string TargetType
        {
            get { return _targetType; }
            set { _targetType = value; }
        }


    }
}
