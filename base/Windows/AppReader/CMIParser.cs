// ----------------------------------------------------------------------------
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
// ----------------------------------------------------------------------------

namespace ManifestReader
{
    using System;
    using System.IO;
    using System.Collections;
    using System.Xml;
    using System.Diagnostics;

	public class CMIParser : XmlManifestParser
	{
		Hashtable parentDirectoriesAlreadySeen;
		string curRegKey;
		public CMIParser() : base()
		{
			curRegKey = "";
			parentDirectoriesAlreadySeen = new Hashtable();
		}

		public override string Classify(string appName, string file, XmlTextReader xmld, Hashtable wxElementTranslator)
		{
			string tagname = xmld.Name;
			if (tagname.Equals("file"))
			{
				string filename = xmld.GetAttribute("name");
				if (filename == null)
				{
					// for those in Microsoft who don't seem to know that XML is case-sensitive
					filename = xmld.GetAttribute("Name");
					if (filename == null)
					{
						filename = xmld.GetAttribute("sourceName");
					}
				}
				
				
				if (filename != null)
				{
					// now register the fact that we provide this file
					string dpath = xmld.GetAttribute("destinationPath");
					if (dpath != null)
					{
						if (dpath.IndexOf("$(runtime.windows)") >= 0)
						{
							dpath = dpath.Replace("$(runtime.windows)", "\\windows");
						}
						else if (dpath.IndexOf("$(runtime.drivers)") >= 0) {
							dpath = dpath.Replace("$(runtime.drivers)", "\\windows\\system32\\drivers");
						}
						else if (dpath.IndexOf("$(runtime.system32)") >= 0) {
							dpath = dpath.Replace("$(runtime.system32)", "\\windows\\system32");
						}

						// make sure that it has no trailing \ and that it starts with a \
						dpath = dpath.TrimEnd(new char[] {'\\'});
						dpath = dpath.TrimStart(new char[] {'\\'});
						dpath = '\\' + dpath;
					}
					ManifestParser.addProvidesFile(dpath == null ? "" : dpath, filename, appName);
				
					if (dpath != null && !dpath.Equals("\\"))
					{
						string[] pathElts = dpath.Split(new char[] {'\\'}, 50);
						string curPath = "";
						for (int i = 0; i < pathElts.Length; i++)
						{
							if (pathElts[i].Equals(""))
							{
								continue;
							}
							string fullPath = curPath;
							if (i != 0)
							{
								fullPath += "\\";
							}
							fullPath += pathElts[i];

							if (parentDirectoriesAlreadySeen.ContainsKey(fullPath))
							{
								curPath = fullPath;
								continue;
							}
							ManifestParser.addProvidesFile(curPath, pathElts[i], appName);
							curPath = fullPath;
							parentDirectoriesAlreadySeen[fullPath] = 1;
						}
					}

					// and parse it to see if it's an interesting file
					string[] components = filename.Split(new char[] {'.'}, 10);
					string suffix = components[components.Length - 1];

					if (isImageSuffix(suffix))
					{
						return "Data File Display UI";
					}
					else if (isFontSuffix(suffix)) {
						return "Data File Display Fonts";
					}
					else {
						return "Data File";
					}
				}
				return "";
			}
			else if (tagname.Equals("fileDependency")) {
				// then register this file dependency
				string filename = xmld.GetAttribute("name");
				if (filename != null)
				{
					// now register the fact that we require this file
					string dpath = xmld.GetAttribute("destinationPath");
					if (dpath != null)
					{
						if (dpath.Equals("$(runtime.windows)"))
						{
							dpath = "\\windows\\system32";
						}
						// make sure that it has no trailing \ and that it starts with a \
						dpath = dpath.TrimEnd(new char[] {'\\'});
						dpath = dpath.TrimStart(new char[] {'\\'});
						dpath = '\\' + dpath;
					}
					ManifestParser.addRequiresFile(dpath == null ? "" : dpath, filename, appName);
					return (string)wxElementTranslator[tagname];
				}
				return "";
			}
			else if (tagname.Equals("IPermission")) {
				// ADD: parse the permissions into types
				return "Access Authentication";
			}
			else if (tagname.Equals("registryKey")) {
				// capture this as the current key
				curRegKey = xmld.GetAttribute("keyName");
				return (string)wxElementTranslator[tagname];
			}
			else if (tagname.Equals("registryValue")) {
				string tempname = xmld.GetAttribute("name");
				string tempval = xmld.GetAttribute("value");
				return this.parseRegistry(curRegKey + "\\" + tempname, tempval, appName);
			}
			else {
				// for now, just look up this element in our translator
				// (this may end up returning null)
				return (string)wxElementTranslator[tagname];
			}
		}
	}
}
