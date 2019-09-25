// ----------------------------------------------------------------------------
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
// ----------------------------------------------------------------------------

using System;
using System.IO;
using System.Xml;
using System.Collections;
using System.Collections.Generic;
using System.Text;
using Microsoft.Build.Framework;

namespace Microsoft.Singularity.BuildTasks
{
    public class Mkmani : ExecTaskBase
    {
        string _outputManifestPath;
        string _applicationName;
        string _cacheRootPath;
        string _outputNativeExecutablePath;
        string _codeGenParameters;
        string _linkerParameters;
        ITaskItem[] _assemblies;

        protected override bool Execute()
        {
            ArrayList codegen = new ArrayList();
            ArrayList linker = new ArrayList();
            string outfile = _outputManifestPath;
            string appname = _applicationName;
            string x86file = _outputNativeExecutablePath;
            string cacheDirectory = _cacheRootPath;

            // check all input files
            ArrayList infiles = new ArrayList();
            foreach (ITaskItem assembly in _assemblies) {
                if (!File.Exists(assembly.ItemSpec)) {
                    LogError(String.Format("Error: Assembly '{0}' not found.", assembly.ItemSpec));
                    return false;
                }
                infiles.Add(assembly.ItemSpec);
            }

            if (!Directory.Exists(cacheDirectory)) {
                LogError(String.Format("Error: Cache directory '{0}' not found.", cacheDirectory));
                return false;
            }

            // This is to work around a bug in ManifestBuilder that causes it to emit paths like
            // cache="/Apps/..." into manifests, which are later interpreted as absolute paths
            // by NIB.
            if (!cacheDirectory.EndsWith("\\"))
                cacheDirectory += "\\";

            // initialize the empty app manifest.
            ManifestBuilder mb = new ManifestBuilder(_cacheRootPath, infiles);

            string nativeExecutableFullPath;
            if (!String.IsNullOrEmpty(_outputNativeExecutablePath))
                nativeExecutableFullPath = Path.GetFullPath(_outputNativeExecutablePath);
            else
                nativeExecutableFullPath = "";

            // create the app manifest
            if (!mb.CreateNewManifest(appname, nativeExecutableFullPath)) {
                LogError("An error occurred while generating the manifest.");
                return false;
            }

            // Add the codegen flags.
            foreach (string param in codegen) {
                mb.AddCodegenParameter(param);
            }

            // Add the linker flags.
            foreach (string param in linker) {
                mb.AddLinkerParameter(param);
            }

            // output the xml document:
            try {
                using (XmlTextWriter writer = new XmlTextWriter(outfile, System.Text.Encoding.UTF8)) {
                    writer.Formatting = Formatting.Indented;
                    mb.Save(writer);
                }
            }
            catch (Exception ex) {
                LogError("The manifest file could not be created: " + ex.Message);
                return false;
            }

            return true;
        }


        [Required]
        public string OutputManifestPath
        {
            get { return _outputManifestPath; }
            set { _outputManifestPath = value; }
        }

        [Required]
        public string ApplicationName
        {
            get { return _applicationName; }
            set { _applicationName = value; }
        }

        [Required]
        public string CacheRootPath
        {
            get { return _cacheRootPath; }
            set { _cacheRootPath = value; }
        }

        [Required]
        public string OutputNativeExecutablePath
        {
            get { return _outputNativeExecutablePath; }
            set { _outputNativeExecutablePath = value; }
        }

        public ITaskItem[] Assemblies
        {
            get { return _assemblies; }
            set { _assemblies = value; }
        }

        public string CodeGenParameters
        {
            get { return _codeGenParameters; }
            set { _codeGenParameters = value; }
        }

        public string LinkerParameters
        {
            get { return _linkerParameters; }
            set { _linkerParameters = value; }
        }
    }

}
