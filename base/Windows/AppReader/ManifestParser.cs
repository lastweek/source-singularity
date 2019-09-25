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

	public abstract class ManifestParser
	{
		public ManifestParser()
		{
			// do nothing for now
		}

		public static Hashtable registryConflictTable = new Hashtable();
		public static Hashtable provideFileTable = new Hashtable();
		public static Hashtable requiresFileTable = new Hashtable();
        public static Hashtable appFileTable = new Hashtable();
        public static Hashtable appRegistryTable = new Hashtable();
        public static Hashtable nameTable = new Hashtable();
		public static Hashtable fileTypeTable = new Hashtable();
		public static Hashtable customActionsTable = new Hashtable();
		public static void addEntry(string path, string val, string appName)
		{
			if (!registryConflictTable.ContainsKey(path))
			{
				registryConflictTable[path] = new ArrayList();
			}
			Pair tempP = new Pair(val, appName);
			((ArrayList)(registryConflictTable[path])).Add(tempP);

            // also compute all the prefixes and put them in the appRegistryTable
            if (!appRegistryTable.ContainsKey(appName)) {
                appRegistryTable[appName] = new Hashtable();
            }
            string prefix = "";
            string[] pathElts = path.Split(new char[] {'\\'}, 40);
            for (int i = 0; i < pathElts.Length; i++) {
                prefix += "\\" + pathElts[i];
                if (!((Hashtable)appRegistryTable[appName]).ContainsKey(prefix)) {
                    ((Hashtable)appRegistryTable[appName])[prefix] = 1;
                }
                else {
                    ((Hashtable)appRegistryTable[appName])[prefix] = (int)((Hashtable)appRegistryTable[appName])[prefix] + 1;
                }
            }
		}

		public static void addCustomAction(string appName)
		{
			if (!customActionsTable.ContainsKey(appName))
			{
				customActionsTable[appName] = 0;
			}
			customActionsTable[appName] = (int)customActionsTable[appName] + 1;
		}

		public static void addProvidesFile(string path, string filename, string appName)
		{

			string file = path + "\\" + filename;
			if (path.Equals("\\"))
			{
				file = "\\" + filename;
			}
			// grab off the suffix and put it in the file extension table
			string[] fileComponents = filename.Split(new char[] {'.'}, 50);
			string extension = fileComponents[fileComponents.Length - 1].ToLower();
			if (fileComponents.Length > 1)
			{
				// then we probably have a real file extension (there's at least on '.')
				if (!fileTypeTable.ContainsKey(appName))
				{
					// this hash maps file types to the count for this manifest
					fileTypeTable[appName] = new Hashtable();
				}

				if (!((Hashtable)fileTypeTable[appName]).ContainsKey(extension))
				{
					((Hashtable)fileTypeTable[appName])[extension] = 0;
				}

				((Hashtable)fileTypeTable[appName])[extension] = (int)((Hashtable)fileTypeTable[appName])[extension] + 1;
			}

			if (!provideFileTable.ContainsKey(file))
			{
				provideFileTable[file] = new ArrayList();
			}
			((ArrayList)provideFileTable[file]).Add(appName);
            
            
            if (!appFileTable.ContainsKey(appName)) {
                appFileTable[appName] = new Hashtable();
            }

            if (!((Hashtable)appFileTable[appName]).ContainsKey(file)) {
                ((Hashtable)appFileTable[appName])[file] = 1;
            }
            else {
                ((Hashtable)appFileTable[appName])[file] =  (int)((Hashtable)appFileTable[appName])[file] + 1;
            }
			return;
		}

		public static void addRequiresFile(string path, string filename, string appName)
		{
			string file = path + "\\" + filename;
			
			if (!requiresFileTable.ContainsKey(file))
			{
				// I don't care if I end up adding it twice: I'll sort it out in the end
				requiresFileTable[file] = new ArrayList();
			}
			((ArrayList)requiresFileTable[file]).Add(appName);
			return;
		}

        public static void setName(string appPathName, string appTrueName)
        {
            nameTable[appPathName] = appTrueName;
            return;
        }

		public abstract Hashtable Parse(string appName, string file, Hashtable elementTranslator);

		protected bool isCodeSuffix(string suffix)
		{
			return suffix.Equals("exe") ||
				suffix.Equals("dll") ||
				suffix.Equals("com") ||
				suffix.Equals("bin") ||
				suffix.Equals("ocx") ||
				suffix.Equals("sys");
		}

		protected bool isImageSuffix(string suffix)
		{
			return suffix.Equals("avi") || 
				suffix.Equals("bmp") || 
				suffix.Equals("gif") || 
				suffix.Equals("tif") || 
				suffix.Equals("xbm") || 
				suffix.Equals("jpg") ||
				suffix.Equals("ico");
		}

		protected bool isFontSuffix(string suffix)
		{
			return suffix.Equals("ttf") || 
				suffix.Equals("fon");
		}

		protected string getCodeType(string suffix)
		{
			if (suffix.Equals("exe") ||
				suffix.Equals("com"))
			{
				return "Code NonLinked";
			}
			else if (suffix.Equals("ocx") ||
				suffix.Equals("sys"))
			{
				return "Code Linked Dynamic";
			}
				// despite the name, if it's a DLL, we can't tell
			else if (suffix.Equals("dll")) {
				return "Code";
			}
			return "Code";
		}


		// grab the Hashtable that will give us the paths for Manifest elements
		public static Hashtable GetManifestHashtable(string filename)
		{
			StreamReader ios = new StreamReader(filename);
			Hashtable outTable = new Hashtable();
			string curLine;
			while ((curLine = ios.ReadLine()) != null)
			{
				// take the first word, and leave the rest
				int firstSpaceIndex = curLine.IndexOf(' ');
				string first = curLine.Substring(0, firstSpaceIndex);
				//"Got first = ***{0}***", first);
				string rest = curLine.Substring(firstSpaceIndex + 1);
				//"Got rest = ***{0}***", rest);
				outTable[first] = rest;
			}
			return outTable;
		}

		protected string parseRegistry(string fullpath, string val, string file)
		{
			// just add this Registry entry to the Hashtable
			ManifestParser.addEntry(fullpath, val, file);

			// split off the first two elements from the path
			string[] components = fullpath.Split(new char[] {'\\'}, 10);
			string rootname = components[0];
			string toplevelname = components[1];
			if (rootname.Equals("HKCR"))
			{
				if (toplevelname.Equals("CLSID") ||
					toplevelname.Equals("Interface"))
				{
					return "Code NonLinked";
				}
			}
			else if (rootname.Equals("HKCU")) {
				if (toplevelname.Equals("Printers"))
				{
					return "Code NonLinked";
				}
			}
			else if (rootname.Equals("HKLM")) {
				if (toplevelname.Equals("HARDWARE"))
				{
					return "Hardware";
				}
				else if (toplevelname.Equals("SYSTEM")) {
					return "Data Config Settings Permanent";
				}
			}
			return "Data Config Settings";
		}
	}
}
