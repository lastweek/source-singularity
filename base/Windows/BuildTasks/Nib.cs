// ----------------------------------------------------------------------------
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
// ----------------------------------------------------------------------------

using System;
using System.Collections.Generic;
using System.Text;
using Microsoft.Build.Framework;

namespace Microsoft.Singularity.BuildTasks
{
    public class Nib : ExecTaskBase
    {
        protected override bool Execute()
        {
            if (_manifests == null || _manifests.Length == 0) {
                LogMessage("No manifests were provided.");
                return false;
            }

            List<String> args = new List<String>();

            if (!String.IsNullOrEmpty(_bartokexepath))
                args.Add("/bartok:" + _bartokexepath);

            if (!String.IsNullOrEmpty(_linkexepath))
                args.Add("/linker:" + _linkexepath);

            if (String.IsNullOrEmpty(_optionsFile)) {
                LogMessage("The 'OptionsFile' parameter is required, but no value was provided.");
                return false;
            }
            args.Add("/options:" + _optionsFile);

            if (String.IsNullOrEmpty(_cachePath)) {
                LogMessage("The 'CachePath' parameter is required, but no value was provided.");
                return false;
            }
            args.Add("/cache:" + _cachePath);

            if (_verboseLogging)
                args.Add("/v");

            if (String.IsNullOrEmpty(_nativeCachePath)) {
                LogMessage("The 'NativeCachePath' parameter is required, but no value was provided.");
                return false;
            }
            args.Add("/libcache:" + _nativeCachePath);

            if (String.IsNullOrEmpty(_nativeExecutableOutputPath)) {
                LogMessage("The 'NativeExecutableOutputPath' parameter is required, but no value was provided.");
                return false;
            }
            args.Add("/native:" + _nativeExecutableOutputPath);

            if (String.IsNullOrEmpty(_nativeObjectPath)) {
                LogMessage("The 'NativeObjectPath' parameter is required, but no value was provided.");
                return false;
            }
            args.Add("/temp:" + _nativeObjectPath);


            if (String.IsNullOrEmpty(TargetArchitecture)) {
                LogMessage("The 'TargetArchitecture' parameter is required, but no value was provided.");
                return false;
            }
            args.Add("/machine:" + TargetArchitecture);

            if (!_buildInParallel)
                args.Add("/par");

            foreach (ITaskItem item in _manifests) {
                if (item == null)
                    continue;
                args.Add(item.ItemSpec);
            }

            return ExecuteProgram(_exepath, args);
        }

        bool _buildInParallel = true;
        public bool BuildInParallel
        {
            get { return _buildInParallel; }
            set { _buildInParallel = value; }
        }


        string _exepath = "nib.exe";
        public string ExecutablePath
        {
            get { return _exepath; }
            set { _exepath = value; }
        }

        string _bartokexepath;
        public string BartokExecutablePath
        {
            get { return _bartokexepath; }
            set { _bartokexepath = value; }
        }

        string _linkexepath;
        public string LinkExecutablePath
        {
            get { return _linkexepath; }
            set { _linkexepath = value; }
        }

        ITaskItem[] _manifests;

        [Required]
        public ITaskItem[] Manifests
        {
            get { return _manifests; }
            set { _manifests = value; }
        }

        string _cachePath;

        /// <summary>
        /// This becomes the /cache: parameter.
        /// </summary>
        [Required]
        public string CachePath
        {
            get { return _cachePath; }
            set { _cachePath = value; }
        }

        bool _forceCompile;

        public bool ForceCompile
        {
            get { return _forceCompile; }
            set { _forceCompile = true; }
        }

        string _nativeExecutableOutputPath;

        [Required]
        public string NativeExecutableOutputPath
        {
            get { return _nativeExecutableOutputPath; }
            set { _nativeExecutableOutputPath = value; }
        }

        /// <summary>
        /// This becomes the /libcache: parameter.
        /// </summary>
        [Required]
        public string NativeCachePath
        {
            get { return _nativeCachePath; }
            set { _nativeCachePath = value; }
        }
        string _nativeCachePath;


        /// <summary>
        /// The path where Bartok stores its object files (app.obj, app_superObj.obj, etc.).
        /// </summary>
        [Required]
        public string NativeObjectPath
        {
            get { return _nativeObjectPath; }
            set { _nativeObjectPath = value; }
        }
        string _nativeObjectPath;


        public string _optionsFile;
        public string OptionsFile
        {
            get { return _optionsFile; }
            set { _optionsFile = value; }
        }


        bool _verboseLogging;
        public bool VerboseLogging
        {
            get { return _verboseLogging; }
            set { _verboseLogging = value; }
        }

        [Required]
        public string TargetArchitecture
        {
            get { return _targetArchitecture; }
            set { _targetArchitecture = value; }
        }
        string _targetArchitecture;

    }
}
