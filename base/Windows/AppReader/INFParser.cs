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

	public class INFParser : ManifestParser
	{
		public override Hashtable Parse(string appName, string file, Hashtable elementTranslator)
		{
			Hashtable outTable = new Hashtable();
			StreamReader ios = new StreamReader(file);

			#region Parse INF File
			ArrayList sections = new ArrayList();
			INFSection curSection = null;
			INFVersionSection versionSection = null;
			INFStringSection strSection = null;
			string curLine = ios.ReadLine();
			while (curLine != null)
			{
				
				// get rid of the whitespace on both sides
				curLine = curLine.Trim();

				if (curLine.Equals("")) 
				{
					curLine = ios.ReadLine();
					continue;
				}
				// we don't like lines that start with control characters
				if (curLine[0] < 32)
				{
					curLine = ios.ReadLine();
					continue;
				}

				if (curLine.StartsWith("#pragma"))
				{
					// I can't believe this is in an INF file!
					curLine = ios.ReadLine();
					continue;
				}

				if (curLine.StartsWith("----"))
				{
					curLine = ios.ReadLine();
					continue;
				}

					//Console.WriteLine(curLine);
				if (INFSection.IsComment(curLine)) 
				{	
					//Console.WriteLine("***Ignoring comment");
					curLine = ios.ReadLine();
					continue;
				}
				if (INFSection.IsSection(curLine))
				{
					//Console.WriteLine("***Found Section");
					if (curSection != null)
					{
						sections.Add(curSection);
					}
					if (INFSection.IsStringSection(curLine))
					{
						//Console.WriteLine("***It's a Strings section");

						curSection = new INFStringSection(curLine);
						strSection = (INFStringSection)curSection;
					}
					else {
						if (INFSection.IsVersionSection(curLine))
						{
							//Console.WriteLine("***It's a version section");

							curSection = new INFVersionSection(curLine);
							versionSection = (INFVersionSection)curSection;
						}
						else {
							curSection = new INFSection(curLine);
						}
					}
					
				}
				else {
					// I can only assume that the real INF parser just ignores
					// everything that's not in a section, given what I've seen
					// at the top of INF files so far
					if (curSection != null)
					{
						//Console.WriteLine("***Adding Line to Section "  + curSection.Name);

						curSection.AddLine(curLine);
					}
				}
				curLine = ios.ReadLine();
			}
			if (curSection != null)
			{
				sections.Add(curSection);
			}
			#endregion

			#region Replace Strings
			//Debug.Assert(versionSection != null);
			// make sure we have a string table somewhere
			if (strSection != null)
			{

				// now grab the INFStringSection and pass it to each INFSection 
				// so they can update their strings to be correct
				for (int i = 0; i < sections.Count; i++)
				{
					((INFSection)sections[i]).UpdateStrings(strSection);
				}
			}
			#endregion

			#region Record Registry Changes

			// now that we've replaced the strings, we can safely 
			// discover all the Registry section lines
			for (int i = 0; i < sections.Count; i++)
			{
				((INFSection)sections[i]).DiscoverRegistryLines();
			}

			// walk the sections again and accumulate all the AddReg and DelReg sections
			Hashtable addRegSections = new Hashtable();
			Hashtable delRegSections = new Hashtable();
			for (int i = 0; i < sections.Count; i++)
			{
				((INFSection)sections[i]).GetAddRegSections(addRegSections);
				((INFSection)sections[i]).GetDelRegSections(delRegSections);
			}

			for (int i = 0; i < sections.Count; i++)
			{
				string secName = ((INFSection)sections[i]).Name;
				if (addRegSections.ContainsKey(secName) ||
					delRegSections.ContainsKey(secName))
				{
					// now walk its lines and enter the registry values
					ArrayList lines = ((INFSection)sections[i]).Lines;
					for (int j = 0; j < lines.Count; j++)
					{
						string line = (string)lines[j];
						if (line.Equals("")) continue;
						string versionGUID = null;
						if (versionSection != null)
						{
							versionGUID = versionSection.Guid;
						}
						string regKey = INFSection.GetRegKey(line, versionGUID);
						if (regKey != null)
						{
							//Console.WriteLine("Got RegKey " + regKey);
							string regValue = INFSection.GetRegValue(line);
							// remove all but the innermost double-quote strings from this value
							int removeCount = 0;
							for (int k = 0; k < regValue.Length; k++)
							{
								if (regValue[k] == '"')
								{
									removeCount++;
								}
							}
							if (removeCount > 0)
							{
								regValue = regValue.TrimStart(new char[] {'"'});
								regValue = regValue.TrimEnd(new char[] {'"'});
								regValue = "\"" + regValue + "\"";
							}
							
							//Console.WriteLine("Got RegValue " + regValue);

							ManifestParser.addEntry(regKey, regValue, appName);
						}
					}
				}
			}


			#endregion

			return outTable;
		}

	}
}
