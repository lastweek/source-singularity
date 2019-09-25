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
    public class GenerateLanguage : ExecTaskBase
    {
        protected override bool Execute()
        {
            List<String> args = new List<String>();

            if (!ValidateCSharpIdentifier("ClassName", _className, false))
                return false;

            if (!ValidateCSharpIdentifier("Namespace", _namespace, true))
                return false;

            if (String.IsNullOrEmpty(_languageFile)) {
                LogError("The 'LanguageFile' parameter is required, but no value was provided.");
                return false;
            }

            if (String.IsNullOrEmpty(_outputFile)) {
                LogError("The 'OutputFile' parameter is required, but no value was provided.");
                return false;
            }

            args.Add(_languageFile);
            args.Add(_className);
            args.Add(_namespace);
            args.Add(_outputFile);

            return ExecuteProgram(_exepath, args);
        }


        string _exepath = "spg.exe";
        public string ExecutablePath
        {
            get { return _exepath; }
            set { _exepath = value; }
        }

        string _languageFile;
        public string LanguageFile
        {
            get { return _languageFile; }
            set { _languageFile = value; }
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

        string _outputFile;
        public string OutputFile
        {
            get { return _outputFile; }
            set { _outputFile = value; }
        }



    }
}
