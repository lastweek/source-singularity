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

	public abstract class XmlManifestParser : ManifestParser
	{

		public override Hashtable Parse(string appName, string wxsFile, Hashtable wxElementTranslator)
		{
			Hashtable outTable = new Hashtable();
            StreamReader ios;
            try {
                ios = new StreamReader(wxsFile);
            }
            catch (System.IO.FileNotFoundException) {
                return outTable;
            }
			XmlTextReader xmld = new XmlTextReader(ios);

			while (xmld.Read())
			{
				string name = xmld.LocalName;
				XmlNodeType xnt = xmld.NodeType;
				//Console.WriteLine("Read a line with " + name);
				if (xnt == XmlNodeType.Element)
				{
					//Console.WriteLine("Reading name " + name + " from XML");
					string path = Classify(appName, wxsFile, xmld, wxElementTranslator);
					//					if (path != null)
					//						"some more ***" + path + "***");
					if (path != null)
					{
						if (outTable.ContainsKey(path))
						{
							outTable[path] = (int)outTable[path] + 1;
						}
						else {
							outTable[path] = 1;
						}
					}
				}
			}
			return outTable;
		}

		public abstract string Classify(string appName, string filename, XmlTextReader xmld, Hashtable wxElementTranslator);

	}
}
