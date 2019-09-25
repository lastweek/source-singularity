// ----------------------------------------------------------------------------
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
// ----------------------------------------------------------------------------

using System;
using System.Collections.Generic;
using System.Text;
using System.Threading;
using System.Diagnostics;
using Microsoft.Build.Framework;

namespace Microsoft.Singularity.BuildTasks
{
    public class Sgc : ExecTaskBase
    {
        override protected bool Execute()
        {
            // Scan the parameters and build the argument list that we will pass to the command-line compiler.

            List<String> args = new List<String>();

            args.Add("/nologo");

            if (String.IsNullOrEmpty(_outputAssembly)) {
                LogError("The 'OutputAssembly' property is required, but no value was provided.");
                return false;
            }
            args.Add("/out:" + _outputAssembly);

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


            if (_no_config)
                args.Add("/noconfig");

            if (_no_stdlib)
                args.Add("/nostdlib");

            if (_allowUnsafeBlocks)
                args.Add("/unsafe+");

            if (_checkOverflow)
                args.Add("/checked+");

            if (_assumeFieldsNonNull)
                args.Add("/assumefieldsnonnull");

            if (_emitDebugInformation) {
                string debugType = _debugType;
                if (String.IsNullOrEmpty(debugType))
                    debugType = "full";

                debugType = debugType.ToLower();
                if (debugType != "full" && debugType != "pdbonly") {
                    LogError(String.Format("The value '{0}' is not valid for the 'DebugType' parameter.", _debugType));
                    LogError("Valid values are 'full' and 'pdbonly'.");
                }

                args.Add("/debug+");
                args.Add("/debug:" + debugType);
            }
            else {
                // no debug info
            }

            if (_optimize)
                args.Add("/optimize+");

            if (_generateFullPaths)
                args.Add("/fullpaths");

            if (!String.IsNullOrEmpty(_stdlib)) {
                args.Add("/stdlib:" + _stdlib);
            }


            string platform_version = _platformVersion;
            if (platform_version != null) {
                platform_version = platform_version.ToLower();
                if (platform_version != "cli1" && platform_version != "cli11" && platform_version != "cli2") {
                    LogError("The value '{0}' is not valid for the 'PlatformVersion' parameter.");
                    LogError("Valid values are 'cli1', 'cli11', and 'cli2'.");
                    return false;
                }
            }
            else {
                platform_version = "cli1";
            }

            string runtime_path = _runtimePath;
            if (String.IsNullOrEmpty(runtime_path)) {
                runtime_path = "";
            }
            args.Add("/platform:" + platform_version + "," + runtime_path);

            if (!String.IsNullOrEmpty(_shadowAssemblyPath))
                args.Add("/shadow:" + _shadowAssemblyPath);

            if (_references != null) {
                foreach (ITaskItem reference in _references) {
                    args.Add("/r:" + reference.ItemSpec);
                }
            }

            if (_sources == null || _sources.Length == 0) {
                LogError("No source files were provided.");
                return false;
            }

            if (!String.IsNullOrEmpty(_defineConstants)) {
                string[] defines = _defineConstants.Split(_define_splits, StringSplitOptions.RemoveEmptyEntries);
                foreach (string define in defines) {
                    if (String.IsNullOrEmpty(define))
                        continue;
                    args.Add("/d:" + define);
                }
            }

            if (_disableNullParameterValidation) {
                args.Add("/disable:nullparametervalidation");
            }

            if (!String.IsNullOrEmpty(_documentationFile)) {
                args.Add("/doc:" + _documentationFile);
            }


            if (!String.IsNullOrEmpty(_disabledWarnings))
                args.Add("/nowarn:" + _disabledWarnings);

            if (_treatWarningsAsErrors)
                args.Add("/warnaserror+");
            
            if (!String.IsNullOrEmpty(_warningsAsErrors))
                args.Add("/warnaserror:" + _warningsAsErrors);

            foreach (ITaskItem source in _sources) {
                args.Add(source.ItemSpec);
            }

            return ExecuteProgram(_sgcExe, args);
        }

        static readonly char[] _define_splits = { ';', ' ', '\t' };

        ITaskItem[] _sources;

        [Required]
        public ITaskItem[] Sources
        {
            get { return _sources; }
            set { _sources = value; }
        }

        string _targetType = "Exe";

        [Required]
        public string TargetType
        {
            get { return _targetType; }
            set { _targetType = value; }
        }

        bool _treatWarningsAsErrors;

        public bool TreatWarningsAsErrors
        {
            get { return _treatWarningsAsErrors; }
            set { _treatWarningsAsErrors = value; }
        }

        int _warningLevel;

        public int WarningLevel
        {
            get { return _warningLevel; }
            set { _warningLevel = value; }
        }

        string _warningsNotAsErrors;
        string _warningsAsErrors;

        public string WarningsAsErrors
        {
            get { return _warningsAsErrors; }
            set { _warningsAsErrors = value; }
        }

        public string WarningsNotAsErrors
        {
            get { return _warningsNotAsErrors; }
            set { _warningsNotAsErrors = value; }

        }

        bool _no_stdlib;

        public bool NoStandardLib
        {
            get { return _no_stdlib; }
            set { _no_stdlib = value; }
        }


        string _stdlib;

        public string StandardLib
        {
            get { return _stdlib; }
            set { _stdlib = value; }
        }

        bool _optimize;

        public bool Optimize
        {
            get { return _optimize; }
            set { _optimize = value; }
        }

        [Required]
        public string OutputAssembly
        {
            get { return _outputAssembly; }
            set { _outputAssembly = value; }
        }

        string _outputAssembly;

        string _platform = "anycpu";

        public string Platform
        {
            get { return _platform; }
            set { _platform = value; }
        }

        ITaskItem[] _references;

        public ITaskItem[] References
        {
            get { return _references; }
            set { _references = value; }
        }

        string _runtimePath;

        public string CompilerRuntimePath
        {
            get { return _runtimePath; }
            set { _runtimePath = value; }
        }

        string _platformVersion = "cli1";

        public string PlatformVersion
        {
            get { return _platformVersion; }
            set { _platformVersion = value; }
        }


        bool _disableNullParameterValidation;
        public bool DisableNullParameterValidation
        {
            get { return _disableNullParameterValidation; }
            set { _disableNullParameterValidation = value; }
        }





        bool _allowUnsafeBlocks;

        public bool AllowUnsafeBlocks
        {
            get { return _allowUnsafeBlocks; }
            set { _allowUnsafeBlocks = value; }
        }

        bool _checkOverflow;
        public bool CheckForOverflowUnderflow
        {
            get { return _checkOverflow; }
            set { _checkOverflow = value; }
        }

        string _debugType;
        public string DebugType
        {
            get { return _debugType; }
            set
            {
                if (value != null) {
                    value = value.ToLower();
                    switch (value) {
                        case "full":
                        case "pdbonly":
                            break;

                        default:
                            throw new ArgumentException("The value provided is not valid for the property DebugType.", "DebugType");
                    }
                    _debugType = value;
                }
                else {
                    _debugType = value;
                }
            }
        }

        string _defineConstants;

        public string DefineConstants
        {
            get { return _defineConstants; }
            set { _defineConstants = value; }
        }

        string _disabledWarnings;

        public string DisabledWarnings
        {
            get { return _disabledWarnings; }
            set { _disabledWarnings = value; }
        }

        string _documentationFile;

        public string DocumentationFile
        {
            get { return _documentationFile; }
            set { _documentationFile = value; }
        }

        bool _emitDebugInformation;

        public bool EmitDebugInformation
        {
            get { return _emitDebugInformation; }
            set { _emitDebugInformation = value; }
        }


        bool _generateFullPaths;

        public bool GenerateFullPaths
        {
            get { return _generateFullPaths; }
            set { _generateFullPaths = value; }
        }

        string _keyContainer;

        public string KeyContainer
        {
            get { return _keyContainer; }
            set { _keyContainer = value; }
        }

        string _keyFile;
        public string KeyFile
        {
            get { return _keyFile; }
            set { _keyFile = value; }
        }

        string _mainEntryPoint;

        public string MainEntryPoint
        {
            get { return _mainEntryPoint; }
            set { _mainEntryPoint = value; }
        }

        string _sgcExe = "sgc.exe";
        public string ExecutablePath
        {
            get { return _sgcExe; }
            set { _sgcExe = value; }
        }

        bool _assumeFieldsNonNull;
        public bool AssumeFieldsNonNull
        {
            get { return _assumeFieldsNonNull; }
            set { _assumeFieldsNonNull = value; }
        }

        string _shadowAssemblyPath;
        public string ShadowAssemblyPath
        {
            get { return _shadowAssemblyPath; }
            set { _shadowAssemblyPath = value; }
        }

        bool _no_config;
        public bool NoConfig
        {
            get { return _no_config; }
            set { _no_config = value; }
        }
    }
}
