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

	public class WiXParser : XmlManifestParser
	{
        string productName = "";
		string currentDir = "";
		public override string Classify(string appName, string file, XmlTextReader xmld, Hashtable wxElementTranslator)
		{
			if (xmld.NodeType == XmlNodeType.EndElement)
			{
				if (xmld.Name.Equals("Directory"))
				{
					// chop off the most recent addition to the directory string
					// and register this "file" with the providesFile table
					// We know that there must be some slash here
					int lastSlash = currentDir.LastIndexOf("\\");
					string providedDir = currentDir.Substring(lastSlash + 1);
					currentDir = currentDir.Substring(0, lastSlash);

					addProvidesFile(currentDir, providedDir, appName);
				}
				return "";
			}
			else {
				if (xmld.Name.Equals("CustomAction"))
				{
					// add this filename to the custom action count
					addCustomAction(appName);
					return "";
				}
				if (xmld.Name.Equals("Product"))
				{
					// get the product name
					productName = xmld.GetAttribute("Name");
					setName(file, productName);
					return "";
				}
				else if (xmld.Name.Equals("Directory")) {
					string dirName = xmld.GetAttribute("LongName");
					if (dirName == null)
					{
						dirName = xmld.GetAttribute("Name");   
					}

					if (dirName.Equals("."))
					{
						dirName = xmld.GetAttribute("LongSource");
						if (dirName == null)
						{
							dirName = xmld.GetAttribute("SourceName");
						}
					}
					if (!xmld.IsEmptyElement)
					{
						// if this element has any children
						// add this string to the directory name
						currentDir += "\\" + dirName;
					}
					else {
						if (dirName != null)
						{
							// otherwise, register it and move on
							addProvidesFile(currentDir, dirName, appName);
						}
					}
					return "";
				}
				else if (xmld.Name.Equals("File")) {
					string filename = xmld.GetAttribute("LongName");
					if (filename == null)
					{
						filename = xmld.GetAttribute("Name");
					}
        
					// add this to the providesFileTable
					addProvidesFile(currentDir, filename, appName);

					//Console.Error.WriteLine(filename);
					string[] components = filename.Split(new char[] {'.'}, 10);
					string suffix = components[components.Length - 1];
					if (isCodeSuffix(suffix))
					{
						return getCodeType(suffix);
					}
					else if (isImageSuffix(suffix)) {
						return "Data File Display UI";
					}
					else if (isFontSuffix(suffix)) {
						return "Data File Display Fonts";
					}
					else {
						return "Data File";
					}
				}
				else if (xmld.Name.Equals("Registry")) {
					// parse the registry prefix
					string rootname = xmld.GetAttribute("Root");
					string path = xmld.GetAttribute("Key");
	
					string fullpath = rootname + "\\" + path;

					string val = xmld.GetAttribute("Value");

					string valname = xmld.GetAttribute("Name");

					return parseRegistry(fullpath + "\\" + valname, val, appName);

				}
				else {
					// look up this element in our translator
					// (this may end up returning null)
					return (string)wxElementTranslator[xmld.Name];
				}
			}
		}

	}
}
