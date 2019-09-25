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

	public class RegINFParser : ManifestParser
	{
						
		public override Hashtable Parse(string appName, string file, Hashtable elementTranslator)
		{
			Hashtable outTable = new Hashtable();
			StreamReader ios = new StreamReader(file);
			string curLine = ios.ReadLine();
			while (curLine != null)
			{
				// each line is just a simple registry line with no strings or substitution
				string regKey = INFSection.GetRegKey(curLine, "");
				string regVal = INFSection.GetRegValue(curLine);
				ManifestParser.addEntry(regKey, regVal, appName);
				curLine = ios.ReadLine();
			}
			return outTable;
		}
	}
}
