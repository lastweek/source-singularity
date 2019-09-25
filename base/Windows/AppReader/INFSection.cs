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

	public class INFSection
	{
		string version;

		public string Version
		{
			get
			{
				return version;
			}
		}

		string name;
		
		public string Name
		{
			get
			{
				return name;
			}
		}


		ArrayList lines;

		public ArrayList Lines
		{
			get
			{
				// return a copy so it can be modified
				return new ArrayList(lines);
			}
		}

		ArrayList addRegSectionNames;
		ArrayList delRegSectionNames;
		public INFSection(string line)
		{
			string temp;
			version = null;

			// you can't just throw away all the characters to the right of the	
			// first ';', 'cause apparently this is a valid character in section identifiers
			// Instead, we will find the '[' ']' and make sure there're only comment
			// strings after it
			int leftBracket = -1;
			int rightBracket = -1;
			for (int i = 0; i < line.Length; i++)
			{
				if (line[i] == '[') leftBracket = i;
				if (line[i] == ']') 
				{
                    if (leftBracket < 0) {
                        throw new Exception("Could not find a left bracket");
                    }
					rightBracket = i;
					break;
				}
			}
			temp = line.Substring(leftBracket, rightBracket-leftBracket+1);
			//Console.WriteLine("Got section title " + temp);
			temp = temp.Trim();
            if (!temp.StartsWith("[") ||
                !temp.EndsWith("]"))
            {
                throw new Exception("The line is not properly bracketed");
            }
			temp = temp.TrimEnd(new char[] {']'});
			temp = temp.TrimStart(new char[] {'['});
			this.name = temp;
			lines = new ArrayList();
			addRegSectionNames = new ArrayList();
			delRegSectionNames = new ArrayList();
		}

		public void GetAddRegSections(Hashtable h)
		{
			for (int i = 0; i < addRegSectionNames.Count; i++)
			{
				h[(string)addRegSectionNames[i]] = null;
			}
			return;
		}
		public void GetDelRegSections(Hashtable h)
		{
			for (int i = 0; i < delRegSectionNames.Count; i++)
			{
				h[(string)delRegSectionNames[i]] = null;
			}
			return;
		}
		
		public void DiscoverRegistryLines()
		{
			for (int i = 0; i < lines.Count; i++)
			{
				string line = (string)lines[i];
				if (line.ToLower().StartsWith("addreg"))
				{
					parseRegLine(line, addRegSectionNames);
				}
				else if (line.ToLower().StartsWith("delreg")) {
					parseRegLine(line, delRegSectionNames);
				}
			}

		}

		public virtual void AddLine(string line)
		{


			// throw away any comments
			string[] parsedLine = line.Split(new char[] {';'}, 20);

			// if this is the Version section, record the ClassID
			if (this is INFVersionSection)
			{
                if (line.ToLower().StartsWith("classguid")) {
					string[] components = parsedLine[0].Split(new char[] {'='}, 2);
					components[1] = components[1].Trim();
					((INFVersionSection)this).Guid = components[1];
				}
			}

			lines.Add(parsedLine[0]);
			return;
		}

		protected void parseRegLine(string line, ArrayList regSectionNames)
		{
			// split on '=' and then on ',' and walk through and add the entries
			string[] twoHalves = line.Split(new char[] {'='}, 2);
            if (twoHalves.Length != 2) {
                throw new Exception(line + " is not a valid registry line");
            }
			// 40 is a magic number.  I have no idea how many there may be, 
			// but I can't imagine there being more than 40 on a single line
			string[] regSections = twoHalves[1].Split(new char[] {','}, 40);
			for (int i = 0; i < regSections.Length; i++)
			{
				string rSec = regSections[i];
				rSec = rSec.Trim();
				regSectionNames.Add(rSec);
			}
			return;
		}

		public void UpdateStrings(INFStringSection strSec)
		{
			// walk through each line and replace its '%'-quoted strings
			for (int i = 0; i < lines.Count; i++)
			{
				string curLine = (string)lines[i];
				string replacementLine = curLine;
				bool insideReplacement = false;
				string curReplace = "";
				int percentCount = 0;
				for (int j = 0; j < curLine.Length; j++)
				{
					if (insideReplacement)
					{
						curReplace += curLine[j];
					}

					if (curLine[j] == '%')
					{
						percentCount++;
						// if we have seen an odd number of '%' and the next character is not a '%'
						if (percentCount % 2 == 1 &&
							!(j < curLine.Length - 1 && curLine[j + 1] == '%'))
						{
							if (insideReplacement)
							{
								// try to replace the string
								if (strSec.hasString(curReplace))
								{
									replacementLine = replacementLine.Replace(curReplace, strSec[curReplace]);
								}
								curReplace = "";
								percentCount = 0;

							}
							insideReplacement = !insideReplacement;
							if (insideReplacement)
							{
								curReplace += curLine[j];
							}
						}
					}
					else {
						percentCount = 0;
					}
				}
				lines[i] = replacementLine;
			}
		}

		public static bool IsStringSection(string line)
		{
			return line.ToLower().StartsWith("[strings]");
		}

		public static bool IsVersionSection(string line)
		{
			return line.ToLower().StartsWith("[version]");
		}

		public static bool IsSection(string line)
		{
			return line.ToLower().StartsWith("[");
		}

		public static bool IsComment(string line)
		{
			return line.ToLower().StartsWith(";");
		}

		// according to ChkINF: # HKR = HKLM,System\CurrentControlSet\Control\Class\{SetupClassGUID}

		public static string GetRegKey(string line, string guid)
		{
			if (!line.StartsWith("HK"))
			{
				return null;
			}
			// if we're not referenced from one of the magic sections, this is easy
			string[] valStr = line.Split(new char[] {','}, 5);
			// the first three entries are the components of the key
			string root = valStr[0];
			root = root.Trim();
            string subkey = "";
            string name = "";
            if (valStr.Length > 1) {
                subkey = valStr[1];
                subkey = subkey.Trim();
                name = "";
            }

			if (root.Equals("HKR"))
			{
				if (guid == null)
				{
					guid = "EVIL_INF";
					//throw new Exception("We have an HKR string, but no version section!");
				}
				root = "HKLM";
				subkey = "System\\CurrentControlSet\\Control\\Class\\" + guid + "\\" + subkey;
				if (valStr.Length > 2)
				{
					name = valStr[2];
				}

			}
			else {
				// trim any outside quotation marks
				subkey = subkey.TrimEnd(new char[] {'"'});
				subkey = subkey.TrimStart(new char[] {'"'});
                if (valStr.Length > 2) {
                    name = valStr[2];
                    name = name.Trim();
                    name = name.TrimEnd(new char[] {'"'});
                    name = name.TrimStart(new char[] {'"'});
                }
			}
			// we ignore registry types for now, although this could in theory bite us,
			// since we could get a false negative
            string toReturn = root;
            if (!subkey.Equals("")) {
                toReturn += "\\" + subkey;
            }
            if (!name.Equals("")) {
                toReturn += "\\" + name;
            }
			return toReturn;

		}

		public static string GetRegValue(string line)
		{
			// this is pretty much always easy, although it can be complicated
			// to tell what type of value this is
			string[] valStr = line.Split(new char[] {','}, 5);
            if (valStr.Length < 5) {
                return "";
            }
			// the last entry is the value
			string val = valStr[4];
			val = val.Trim();
			return valStr[4];

		}
	}
}
