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

	public class INFStringSection : INFSection
	{
		Hashtable stringTable;
		public INFStringSection(string line) : base(line)
		{
			stringTable = new Hashtable();
		}
	
		public bool hasString(string str)
		{
			return stringTable.ContainsKey(str);
		}

		public override void AddLine(string line)
		{
			// parse out the two parts of this line
			// (poor man's evil character removal: this also disallows nonASCII Unicode)
			if (line[0] > 256) return;
			string[] stringAndValue = line.Split(new char[] {'='}, 2);
			// trim final space
            if (stringAndValue.Length != 2) {
                // then this is not a valid INF line.  We'll just ignore it.
                // This behaviour seems to be more consistent with standard INF parsing, unfortunately
                return;
            }
			stringAndValue[0] = stringAndValue[0].Trim();
			stringAndValue[1] = stringAndValue[1].Trim();
			
			// throw out the outermost pair of double quotation marks
			bool startingQuote = stringAndValue[1].StartsWith("\"");
			bool endingQuote = stringAndValue[1].EndsWith("\"");
			if (startingQuote == endingQuote)
			{
				stringAndValue[1] = stringAndValue[1].TrimStart(new char[] {'"'});
				stringAndValue[1] = stringAndValue[1].TrimEnd(new char[] {'"'});
			}

			//Console.WriteLine("Adding %" + stringAndValue[0] + "% = " + stringAndValue[1]);
			this["%" + stringAndValue[0] + "%"] = stringAndValue[1];
			return;
		}

		public string this[string name]
		{
			get
			{
				return (string)stringTable[name];
			}
			set
			{
				// EVIL: you shouldn't have two variable definitions that differ
				// like this.
				//Debug.Assert(!stringTable.ContainsKey(name));
				stringTable[name] = value;
				return;
			}
		}

	}
}
