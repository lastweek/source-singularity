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
    public class Mkasm : ExecTaskBase
    {
        protected override bool Execute()
        {
            List<String> args = new List<String>();


            if (String.IsNullOrEmpty(_outputMode)) {
                LogError("The 'OutputMode' parameter is required, but no value has been provided.");
                LogError("Valid values are 'pecoff' and 'binary'.");
                return false;
            }
            else if (String.Compare(_outputMode, "binary", StringComparison.OrdinalIgnoreCase) == 0) {
                args.Add("/b");
            }
            else if (String.Compare(_outputMode, "pecoff", StringComparison.OrdinalIgnoreCase) == 0) {
                // no arg needed -- it's the default
            }
            else {
                LogError("The value '{0}' is not valid for the 'OutputMode' parameter.");
                LogError("Valid values are 'pecoff' and 'binary'.");
                return false;
            }

            if (String.IsNullOrEmpty(_outputLanguage)) {
                LogError("The 'OutputLanguage' parameter is required, but no value has been provided.");
                LogError("Valid values are 'ASM' and 'C#'.");
                return false;
            }
            else if (String.Compare(_outputLanguage, "asm", StringComparison.OrdinalIgnoreCase) == 0) {
                args.Add("/a");
            }
            else if (String.Compare(_outputLanguage, "C#", StringComparison.OrdinalIgnoreCase) == 0) {
                args.Add("/m");

                if (!ValidateCSharpIdentifier("ClassName", _className, false))
                    return false;

                if (!ValidateCSharpIdentifier("Namespace", _namespace, true))
                    return false;

                if (!ValidateCSharpIdentifier("FieldName", _fieldName, false))
                    return false;

                args.Add("/n:" + _namespace);
                args.Add("/c:" + _className);
                args.Add("/f:" + _fieldName);
            }
            else {
                LogError("The value '{0}' is not valid for the 'OutputLanguage' parameter.");
                LogError("Valid values are 'ASM' and 'C#'.");
                return false;
            }

            if (String.IsNullOrEmpty(_outputFile)) {
                LogError("The 'OutputFile' parameter is required, but no value has been provided.");
                return false;
            }

            args.Add("/o:" + _outputFile);

            if (!String.IsNullOrEmpty(_rootLabel))
                args.Add("/r:" + _rootLabel);

            if (_useBmpCompression)
                args.Add("/x");

            if (_outputAsArray)
                args.Add("/l");

            if (_pecoff64)
                args.Add("/64");

            if (_inputFiles == null || _inputFiles.Length == 0) {
                LogError("No input files were provided.");
                return false;
            }

            foreach (ITaskItem item in _inputFiles) {
                args.Add(item.ItemSpec);
            }

            return ExecuteProgram(_exepath, args);
        }


        string _exepath = "mkasm.exe";
        public string ExecutablePath
        {
            get { return _exepath; }
            set { _exepath = value; }
        }



        string _outputMode;
        /// <summary>
        /// One of "binary" or "pecoff".
        /// </summary>
        [Required]
        public string OutputMode
        {
            get { return _outputMode; }
            set { _outputMode = value; }
        }

        string _outputFile;
        [Required]
        public string OutputFile
        {
            get { return _outputFile; }
            set { _outputFile = value; }
        }

        bool _outputAsArray;
        public bool OutputAsArray
        {
            get { return _outputAsArray; }
            set { _outputAsArray = value; }
        }

        string _rootLabel;
        public string RootLabel
        {
            get { return _rootLabel; }
            set { _rootLabel = value; }
        }

        string _outputLanguage;
        /// <summary>
        /// Valid values are 'asm' and 'c#'.
        /// </summary>
        [Required]
        public string OutputLanguage
        {
            get { return _outputLanguage; }
            set { _outputLanguage = value; }
        }

        string _className;
        public string ClassName
        {
            get { return _className; }
            set { _className = value; }
        }

        string _namespace;
        public string Namespace
        {
            get { return _namespace; }
            set { _namespace = value; }
        }

        public string _fieldName;
        public string FieldName
        {
            get { return _fieldName; }
            set { _fieldName = value; }
        }

        bool _useBmpCompression;
        public bool UseBmpCompression
        {
            get { return _useBmpCompression; }
            set { _useBmpCompression = value; }
        }

        bool _pecoff64;
        public bool InputImagesAre64Bit
        {
            get { return _pecoff64; }
            set { _pecoff64 = value; }
        }

        ITaskItem[] _inputFiles;
        [Required]
        public ITaskItem[] InputFiles
        {
            get { return _inputFiles; }
            set { _inputFiles = value; }
        }

    }
}
