// ----------------------------------------------------------------------------
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
// ----------------------------------------------------------------------------

using System;
using ManifestReader;
using System.Collections;
using System.Diagnostics;
using System.IO;
namespace AppReader
{
	class ReaderMain
	{
		static void Usage()
		{
			Console.WriteLine("AppReader.exe <manifestfile | (-d | -s) manifestdirectory | -r appdirectory>");
			return;
		}

        static double computeSpread(int[] directoryCounts)
        {
            double count = 0;
            for (int i = 0; i < directoryCounts.Length; i++) {
                int curLevelCount = directoryCounts[i];
                count += Math.Pow(100, -i)*(curLevelCount - 1);
            }
            return count;
        }


		static int getAppNumber(string name, Hashtable appNameTable, ref int nameCount)
		{
			if (!appNameTable.ContainsKey(name))
			{
				appNameTable[name] = nameCount++;
			}
			return (int)appNameTable[name];
		}

		static void parseFile(string appName, string file)
		{
			ManifestParser mp;
			// get the suffix
			string[] components = file.Split(new char[] {'.'}, 50);
			string suffix = components[components.Length - 1];
			if (suffix.Equals("wxs"))
			{
				mp = new WiXParser();
			}
			else if (suffix.ToLower().Equals("man") ||
				suffix.ToLower().Equals("manifest"))
			{
				mp = new CMIParser();
			}
			else if (suffix.Equals("inf")) {
				mp = new INFParser();
			}
			else if (suffix.Equals("inft")) {
				mp = new RegINFParser();
			}
			else {
				//Console.WriteLine("Unknown manifest suffix " + suffix);
				return;
			}

			// otherwise, try to parse it
            try {
                mp.Parse(appName, file, new Hashtable());
            }
            catch (System.Xml.XmlException) {
                Console.WriteLine("Could not parse " + file);
            }
//            catch(System.Exception e)
//            {
//                Console.WriteLine("Failed to parse " + file + " : " + e.Message);
//            }
			return;
		}

		static Hashtable parseFile(string appName, string file, Hashtable wxsvals, Hashtable cmivals)
		{
			Hashtable whash = new Hashtable();;
			ManifestParser mp;
			Hashtable inHash;
			// get the suffix
			string[] components = file.Split(new char[] {'.'}, 50);
			string suffix = components[components.Length - 1];
			if (suffix.Equals("wxs"))
			{
				inHash = wxsvals;
				mp = new WiXParser();
			}
			else if (suffix.ToLower().Equals("man") ||
				suffix.ToLower().Equals("manifest"))
			{
				inHash = cmivals;
				mp = new CMIParser();
			}
			else if (suffix.Equals("inf")) {
				inHash = null;
				mp = new INFParser();
			}
			else if (suffix.Equals("inft")) {
				inHash = null;
				mp = new RegINFParser();
			}
			else {
				Console.WriteLine("Unknown manifest suffix " + suffix);
				return whash;
			}

			// otherwise, try to parse it
			try
			{
				whash = mp.Parse(appName, file, inHash);
			}
			catch (System.Xml.XmlException) {
				Console.WriteLine("Could not parse " + file);
			}
			return whash;
		}

		static bool sameApp(string first, string second)
		{
			// we'll compute a heuristic measure of similarity by checking 
			// the number of elements they have in common in 
			// their strings.  Any difference of 2 or less and 
			// we will say that they are the same	
			string[] firstArray = first.Split(new char[] {'.', '_'}, 40);
			string[] secondArray = second.Split(new char[] {'.', '_'}, 40);
			Hashtable firstHash = new Hashtable();
			for (int i = 0; i < firstArray.Length; i++)
			{
				if (!firstHash.ContainsKey(firstArray[i]))
				{
					firstHash[firstArray[i]] = 0;
				}
				firstHash[firstArray[i]] = (int)firstHash[firstArray[i]] + 1;
			}

			for (int i = 0; i < secondArray.Length; i++)
			{
				if (firstHash.ContainsKey(secondArray[i]))
				{
					firstHash[secondArray[i]] = (int)firstHash[secondArray[i]] - 1;
				}
			}

			ICollection vcol = firstHash.Values;
			IEnumerator ienum = vcol.GetEnumerator();
			int sum = 0;
			while (ienum.MoveNext())
			{
				sum += (int)ienum.Current;
			}
			return System.Math.Abs(sum) <= 2;
		}

		[STAThread]
		static void Main(string[] args)
		{
			if (args.Length < 1)
			{
				Usage();
				return;
			}
			#region Setup Variables
			// grab a new app tree
			//AppTree tempat = AppTree.CreateAppTree(args[0]);

			//ArrayList tempar = tempat.Flatten();
			// ... that we can spit out for clustering
			//for(int j = 0; j < tempar.Count; j++)
			//{
			//	Console.Write(((AppNode)tempar[j]).Name + "\t");
			//}
			//Console.WriteLine();
	
			// get the mapping from WiX elements to app tree paths
			//Hashtable wxvals = WiXParser.GetManifestHashtable(args[1]);

			// get the mapping from CMI elements to app tree paths
			//Hashtable cmivals = CMIParser.GetManifestHashtable(args[2]);

			#endregion

            bool doConflictsAndDependencies = true;
            if (args[0].Equals("-s")) {
                doConflictsAndDependencies = false;
            }

			#region Parse Directory
            if (args[0].Equals("-r")) {
                // the next argument must be a directory that 
                // we can parse to get a list of directories that map to apps
                if (args.Length != 2) {
                    Usage(); 
                    return;
                }
                string dir = args[1];
                DirectoryInfo di = new DirectoryInfo(dir);
                if (!di.Exists) {
                    Console.WriteLine("Directory " + dir + " does not exist");
                    return;
                }
                DirectoryInfo[] dis = di.GetDirectories();
                for (int i = 0; i < dis.Length; i++) {
                    DirectoryInfo tempDi = dis[i];
			
					// if this directory itself contains directories, 
					// step into them to get each app
					DirectoryInfo[] subDirs = tempDi.GetDirectories();
					if (subDirs.Length > 0)
					{
						for (int j = 0; j < subDirs.Length; j++)
						{
							DirectoryInfo subDir = subDirs[j];
							string appName = tempDi.Name + " " + subDir.Name;
							FileInfo[] fis = subDir.GetFiles();
							for (int k = 0; k < fis.Length; k++)
							{
								parseFile(appName, subDir.FullName + "\\" + fis[k].Name);  
							}

						}
					}
					else {
						string appName = tempDi.Name;
						FileInfo[] fis = tempDi.GetFiles();
						for (int j = 0; j < fis.Length; j++)
						{
							parseFile(appName, tempDi.FullName + "\\" + fis[j].Name);  
						}
					}
                }
            }
			else if (args[0].Equals("-d") || args[0].Equals("-s")) {
				// the next argument must be a directory that 
				// contains a set of .wxs files for us to parse
				if (args.Length != 2)
				{
					Usage(); 
					return;
				}
                Console.WriteLine("About to parse " + args[1]);
                int count = 0;
				string dir = args[1];
				DirectoryInfo di = new DirectoryInfo(dir);
				if (!di.Exists)
				{
					Console.WriteLine("Directory " + dir + " does not exist");
					return;
				}
				FileInfo[] fis = di.GetFiles();
				
//				Console.WriteLine("Got here with size " + fis.Length);

				// for each manifest file
				for (int i = 0; i < fis.Length; i++)
				{
                    Console.WriteLine(++count);
					// grab a new app tree
					//AppTree at = AppTree.CreateAppTree(args[0]);

					//Hashtable whash = parseFile(fis[i].DirectoryName + "\\" + fis[i].Name, wxvals, cmivals);
					parseFile(fis[i].DirectoryName + "\\" + fis[i].Name, fis[i].DirectoryName + "\\" + fis[i].Name);
					// then set up the app tree
					//at.IncrementWithHashtable(whash);

					// and flatten it to a point in R^n
					//ArrayList ar = at.Flatten();

					//Console.Write(fis[i].Name + "\t");

					// ... that we can spit out for clustering
					//for(int j = 0; j < ar.Count; j++)
					//{
					//	Console.Write(((AppNode)ar[j]).Weight() + "\t");
					//}
					//Console.WriteLine();
				}
			}
				#endregion
				#region Parse Single File
			else {
				if (args.Length != 1)
				{
					Usage(); 
					return;
				}
				// grab a new app tree
				//AppTree at = AppTree.CreateAppTree(args[0]);

                Console.WriteLine("about to parse file");
				//Hashtable whash = parseFile(args[3], wxvals, cmivals);
				parseFile(args[0], args[0]);
				//at.IncrementWithHashtable(whash);
				//at.Dump();
			}
			#endregion
    

            #region Enumerate Registry Dependencies
            Console.WriteLine("---Registry Conflicts---");
            // this Hashtable will contain all the names found in the conflict table
            // and the other apps with which they conflict on registry key/value pairs.
            Hashtable appConflicts = new Hashtable();

            // this table will be used to reduce the size of the generated file
            Hashtable appNameTable = new Hashtable();
            int nameCount = 0;
            if (doConflictsAndDependencies) {

                // now walk the Hashtable and dump any conflicts
                Hashtable conflictTable = ManifestParser.registryConflictTable;
                IDictionaryEnumerator iDictEnum = conflictTable.GetEnumerator();
                while (iDictEnum.MoveNext()) {
                    if (((ArrayList)iDictEnum.Value).Count > 1) {
                        // then we might have a conflict
                        ArrayList confs = ((ArrayList)iDictEnum.Value);
                        string val = (string)((Pair)confs[1]).First;
                        string appname = (string)((Pair)confs[1]).Second;
                        bool founddifference = false;
                        bool foundtwoapps = false;
                        for (int i = 0; i < confs.Count; i++) {
                            Pair outp = (Pair)confs[i];
                            string newval = (string)((Pair)confs[i]).First;
                            string newappname = (string)((Pair)confs[i]).Second;
                            if ((val == null && newval == null) || 
                                (val != null && newval != null && val.ToLower().Equals(newval.ToLower()))) 
                            {
                                continue;
                            }

                            // heuristic (may give some false negatives, but then we're just underestimating a bit)

                            // if one of these starts with a '[' in the first two characters,
                            // then it's probably just a substitution that we didn't notice.
                            // In that case, claim that it is not a conflict
                            if ((val != null && val.Length > 1 && val[0] == '[') ||
                                (val != null && val.Length > 2 && val[1] == '[') ||
                                (newval != null && newval.Length > 1 && newval[0] == '[') ||
                                (newval != null && newval.Length > 2 && newval[1] == '['))
                            {
                                continue;
                            }
                            founddifference = true;
                            if (newappname.Equals(appname)) continue;
                            foundtwoapps = true;
                        }

                        if (!founddifference || !foundtwoapps) continue;

                        Console.WriteLine("C: " + ((string)iDictEnum.Key) + " : " + ((ArrayList)iDictEnum.Value).Count);

                        Hashtable confHash = new Hashtable();
                        for (int i = 0; i < confs.Count; i++) {
                            Pair outp = (Pair)confs[i];
                            string confAppName = (string)outp.Second;
                            if (!appConflicts.ContainsKey(confAppName)) {
                                appConflicts[confAppName] = new Hashtable();
                            }
                            // write the conflicting app into the hash with its value
                            confHash[confAppName] = (string)outp.First;
                            Console.WriteLine("\t " + 
                                getAppNumber((string)outp.Second, appNameTable, ref nameCount)
                                + " writes " + (string)outp.First);
                        }

                        IDictionaryEnumerator iconf1 = confHash.GetEnumerator();
                        while (iconf1.MoveNext()) {
                            string confAppName = (string)iconf1.Key;
                            string confVal1 = (string)iconf1.Value;
                            Hashtable htable = (Hashtable)appConflicts[confAppName];
                            IDictionaryEnumerator iconf2 = confHash.GetEnumerator();
                            while (iconf2.MoveNext()) {
                                string curAppName = (string)iconf2.Key;
                                string confVal2 = (string)iconf2.Value;

                                // don't add this conflict if they are the same app
                                if (curAppName.Equals(confAppName)) continue;
		
                                // don't add this conflict if they have the same value on this key
                                if (confVal2 == null && confVal1 == null) {
                                    continue;
                                }
                                else if (confVal2 != null && confVal1 != null && confVal2.ToLower().Equals(confVal1.ToLower())) {
                                    continue;
                                }

                                if (!htable.ContainsKey(curAppName)) {
                                    htable[curAppName] = 0;
                                }
                                htable[curAppName] = (int)htable[curAppName] + 1;
                            }
                        }

                    }
                }

                IDictionaryEnumerator iDE = appConflicts.GetEnumerator();
                while (iDE.MoveNext()) {
                    string firstName = (string)iDE.Key;
                    Hashtable confvals = (Hashtable)iDE.Value;
                    IDictionaryEnumerator iDEInner = confvals.GetEnumerator();
                    while (iDEInner.MoveNext()) {
                        string secondName = (string)iDEInner.Key;
                        int strength = (int)iDEInner.Value;

                        Console.WriteLine(getAppNumber(firstName, appNameTable, ref nameCount)
                            + "\t" + getAppNumber(secondName, appNameTable, ref nameCount)
                            + "\t" + strength);
                    }
                }

                #endregion

                #region Enumerate File Dependencies

                Console.WriteLine("---File Dependencies---");
                // now let's display all the file dependencies.
                // We'll walk through the ManifestParser.provideFileTable 
                // and ManifestParser.requireFileTable
                IDictionaryEnumerator ireq = ManifestParser.requiresFileTable.GetEnumerator();
                while (ireq.MoveNext()) {
                    string requiredFile = (string)ireq.Key;
                    ArrayList reqArray = (ArrayList)ireq.Value;
                    for (int i = 0; i < reqArray.Count; i++) {
                        string requiringAppName = (string)reqArray[i];
                        if (!ManifestParser.provideFileTable.ContainsKey(requiredFile)) {
                            // do nothing about it for now
                            //throw new Exception("File " + requiredFile + " is required but not provided!");
                        }
                        else {
                            // otherwise, we'll walk through all the apps that provide
                            // this file and print a dependency between them
                            ArrayList provArray = (ArrayList)ManifestParser.provideFileTable[requiredFile];
                            for (int j = 0; j < provArray.Count; j++) {
                                string providingAppName = (string)provArray[j];
                                Console.WriteLine(getAppNumber(requiringAppName, appNameTable, ref nameCount) + "\t" + 
                                    getAppNumber(providingAppName, appNameTable, ref nameCount));
                            }
                        }
                    }
                }	
                #endregion
            }


            #region Evaluate File Spread
            
            Console.WriteLine("\n---File Spread---\n");

            // we use the appFileTable for each app to compute this
            IDictionaryEnumerator appFileEnum = ManifestParser.appFileTable.GetEnumerator();
            while (appFileEnum.MoveNext()) {
                string appName = (string)appFileEnum.Key;
                Hashtable appFiles = (Hashtable)appFileEnum.Value;
                // walk through the list and figure out how many unique prefixes there are of each length
                IDictionaryEnumerator lengthEnum = appFiles.GetEnumerator();
                int max = 0;
                while (lengthEnum.MoveNext()) {
                    string path = (string)lengthEnum.Key;
                    string[] pathElts = path.Split(new char[] {'\\'}, 40);
                    // since the paths all start with \ and 
                    // we don't want to count the empty first pathElt
                    int length = pathElts.Length - 1; 
                    if (length > max) {
                        max = length;
                    }
                }

                int[] lengths = new int[max];

                for (int i = 0; i < lengths.Length; i++) {
                    lengths[i] = 0;
                }

                lengthEnum.Reset();

                while (lengthEnum.MoveNext()) {
                    string path = (string)lengthEnum.Key;
                    string[] pathElts = path.Split(new char[] {'\\'}, 40);
                    // since the paths all start with \ and 
                    // we don't want to count the empty first pathElt
                    int length = pathElts.Length - 1; 
                    // this -1 is because the lengths array is 0-based
                    lengths[length - 1]++;
                }

				for (int i = 0; i < lengths.Length; i++)
				{
					if (lengths[i] == 0)
					{
						lengths[i] = 1;
					}
				}

                double spread = computeSpread(lengths);
                // look up the real name
                if (ManifestParser.nameTable.ContainsKey(appName)) {
                    appName = (string)ManifestParser.nameTable[appName];
                }

                string strSpread = "";
                for (int i = 0; i < lengths.Length; i++) {
                    if (i != 0) {
                        strSpread += " ";
                    }
                    strSpread += lengths[i];
                }
                Console.WriteLine(appName + " : " + spread + " : " + strSpread);
            }
            
            #endregion

            #region Evaluate Registry Spread
            
            Console.WriteLine("\n---Registry Spread---\n");

            // we use the appFileTable for each app to compute this
            IDictionaryEnumerator appRegistryEnum = ManifestParser.appRegistryTable.GetEnumerator();
            while (appRegistryEnum.MoveNext()) {
                string appName = (string)appRegistryEnum.Key;
                Hashtable appRegs = (Hashtable)appRegistryEnum.Value;
                // walk through the list and figure out how many unique prefixes there are of each length
                IDictionaryEnumerator lengthEnum = appRegs.GetEnumerator();
                int max = 0;
                while (lengthEnum.MoveNext()) {
                    string path = (string)lengthEnum.Key;
                    string[] pathElts = path.Split(new char[] {'\\'}, 40);
                    // since the paths all start with \ and 
                    // we don't want to count the empty first pathElt
                    int length = pathElts.Length - 1; 
                    if (length > max) {
                        max = length;
                    }
                }

                int[] lengths = new int[max];

                for (int i = 0; i < lengths.Length; i++) {
                    lengths[i] = 0;
                }

                lengthEnum.Reset();

                while (lengthEnum.MoveNext()) {
                    string path = (string)lengthEnum.Key;
                    string[] pathElts = path.Split(new char[] {'\\'}, 40);
                    // since the paths all start with \ and 
                    // we don't want to count the empty first pathElt
                    int length = pathElts.Length - 1; 
                    // this -1 is because the lengths array is 0-based
                    lengths[length - 1]++;
                }
				for (int i = 0; i < lengths.Length; i++)
				{
					if (lengths[i] == 0)
					{
						lengths[i] = 1;
					}
				}

                double spread = computeSpread(lengths);
                // look up the real name
                if (ManifestParser.nameTable.ContainsKey(appName)) {
                    appName = (string)ManifestParser.nameTable[appName];
                }

                string strSpread = "";
                for (int i = 0; i < lengths.Length; i++) {
                    if (i != 0) {
                        strSpread += " ";
                    }
                    strSpread += lengths[i];
                }
                Console.WriteLine(appName + " : " + spread + " : " + strSpread);

            }
            
            #endregion

	
			#region Print Custom Actions

			Console.WriteLine("---Custom Actions---");

			// walk through the ManifestParser.customActionsTable
			IDictionaryEnumerator customEnum = ManifestParser.customActionsTable.GetEnumerator();
			while (customEnum.MoveNext())
			{
				string appName = (string)customEnum.Key;
				int customCount = (int)customEnum.Value;
				Console.WriteLine(appName + " : " + customCount);
			}

			#endregion

			#region Print File Extensions and Counts

			Console.WriteLine("---File Extensions---");

			// walk through the ManifestParser.fileTypeTable
			IDictionaryEnumerator fileEnum = ManifestParser.fileTypeTable.GetEnumerator();
			while (fileEnum.MoveNext())
			{
				int uniqueFileTypes = 0;
				string appName = (string)fileEnum.Key;
				Hashtable exts = (Hashtable)fileEnum.Value;
				IDictionaryEnumerator extEnum = exts.GetEnumerator();
				while (extEnum.MoveNext())
				{
					uniqueFileTypes++;
					string extension = (string)extEnum.Key;
					int extCount = (int)extEnum.Value;
					Console.WriteLine(appName + " : " + extension + " : " + extCount);
				}
				Console.WriteLine(appName + " : " + uniqueFileTypes);
			}

			#endregion


            #region Print Name Table
			Console.WriteLine("\n---Name Table---\n");

			// now write out the name table
			IDictionaryEnumerator iDENT = appNameTable.GetEnumerator();
			while (iDENT.MoveNext())
			{
                string appName = "";
                // look up the real name
                if (ManifestParser.nameTable.ContainsKey((string)iDENT.Key)) {
                    appName = (string)ManifestParser.nameTable[(string)iDENT.Key];
                }

                if (appName.Equals("")) {
                    Console.WriteLine((string)iDENT.Key + " " + (int)iDENT.Value);
                }
                else {
                    Console.WriteLine((string)iDENT.Key + " " + appName + " " + (int)iDENT.Value);
                }
			}
			#endregion
            return;
	}


	}
}
