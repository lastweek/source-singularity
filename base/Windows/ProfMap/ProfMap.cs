// ----------------------------------------------------------------------------
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
// ----------------------------------------------------------------------------

using System;
using System.Collections;
using System.Globalization;
using System.IO;

namespace ProfMap
{
	/// <summary>
	/// ProfMap is a quick and dirty utility that is used to post-process the result
    // of profiling a Singularity application.  The log contains entries with EIP values
    // rather than symbolic names.  By consulting the Map for the application, we can
    // replace those EIP values with symbolic names, prior to feeding the log to the
    // Profiler.
	/// </summary>


    // Here's an example of a source line we would like to update:
    //
    //           f 0x8 Function_EIP_0x120f32b4 (UNKNOWN ARGUMENTS) 0 0
    //
    // If we find that EIP value 0x120f32b4 is contained within System.RuntimeType.Name's
    // property getter, and that method starts at offset 120f3200, we would rewrite this
    // as:
    //
    //           f 0x8 ?m_get$_Name@Class_System_RuntimeType@@SIPAUClass_System_String@@PAU1@@Z (UNKNOWN ARGUMENTS) 0x120f3200 1
    //
    // If you don't like mangled names, feel free to add an unmangler at AddMapEntry below.
    // This would make it much easier to read the profiles in CLR Profiler.
    //
    // The following app is very brittle if the log format or map format changes.  Also
    // it uses heuristics to determine where the image was loaded into memory so it can
    // bias the EIPs back to image addresses.  These heuristics are brittle.
    
    public class ProfMap
    {
        internal class Entry : IComparable
        {
            internal string symbol;
            internal ulong  addr;

            // Always sort on address, since that is the typical lookup
            public int CompareTo(Object o)
            {
                Entry other = (Entry) o;
                return (addr > other.addr
                        ? 1
                        : (addr == other.addr
                           ? 0
                           : -1));
            }
        }

        static ArrayList    entries;

        static StreamReader logStream, mapStream;
        static StreamWriter newStream;

        static ulong        loadBias;

        // In order to calculate the load address of our image into memory, we need to find
        // a well-known symbol in the map.
        static ulong FindWriteHeader()
        {
            // For WebServer.x86, the symbol we need is represented in the map as:
            //
            // ?m_WriteHeader@Class_Microsoft_Singularity_WebServer_CLRProfiler@@SIXPAU1@PAUClass_Microsoft_Singularity_WebServer_CLRProfiler_Buffer@@@Z
            //
            // Of course, the Microsoft_Singularity_WebServer part is application-specific.
            // So the fragments we are looking for are:
            //
            //    ?m_WriteHeader@Class_ +
            //    <application> +
            //    _CLRProfiler@@SIXPAU1@PAU +
            //    <application> +
            //    _CLRProfiler_Buffer@@@Z
            //
            // We only do this operation once, so a linear search isn't outrageous
            foreach (Entry e in entries) {
                int index1 = e.symbol.IndexOf("?m_WriteHeader@Class_");
                if (index1 >= 0) {
                    int index2 = e.symbol.IndexOf("_CLRProfiler@@SIXPAU1@PAU", index1 + 21);
                    if (index2 >= 0) {
                        int index3 = e.symbol.IndexOf("", index2 + 24);
                        if (index3 >= 0) {
                            return e.addr;
                        }
                    }
                }
            }
            Console.WriteLine("Failure: Couldn't discover the WriteHeader symbol in this map");
            return 0;
        }

        static Entry FindEntry(ulong eip)
        {
            Entry temp = new Entry();
            temp.addr =  eip - loadBias;        // convert from physical to map addresses
            int res = entries.BinarySearch(temp);

            // If we get a negative entry, it's not an exact match.  But it gives us the index of
            // the next largest entry.  Of course, we want the index of the prior entry, since that
            // should cover our address.  At least, that's what MSDN says.  I'm obviously doing
            // something wrong, because I'm off by one.
            if (res < 0) {
                res = -res - 2;
            }
            return (Entry) entries[res];
        }

        static void AddMapEntry(ulong addr, String symbol)
        {
            Entry e = new Entry();
            e.symbol = symbol;
            e.addr = addr;

            entries.Add(e);
        }

        static void ReadMap()
        {
            string textSection = "0001:";           // it usually is, but we will check
            bool   defaultTextSection = true;

            Console.WriteLine("Reading map ");
            AddMapEntry(~(ulong) 0, "Unknown Address");

            int counter = 0;

            while (true) {
                // End of file?
                String line = mapStream.ReadLine();
                if (line == null) {
                    break;
                }

                // read the section table and find the section containing ".text"
                if (defaultTextSection &&
                    line.IndexOf(".text") > 0 &&
                    line.IndexOf("CODE") > 0) {
                    textSection = line.Substring(1, 5);
                    Console.WriteLine("Updating text Section to {0}", textSection);
                    defaultTextSection = false;     // stop looking
                    continue;
                }

                if (line.Length > 31 && line.Substring(1, 5) == textSection) {
                    if ((counter++ % 500) == 0)
                        Console.Write(".");
                    ulong  addr = ulong.Parse(line.Substring(6, 8), NumberStyles.HexNumber);
                    int    temp = line.IndexOf(" ", 21);
                    String symbol = (temp > 21
                                     ? line.Substring(21, temp - 21)
                                     : line.Substring(21));
                    AddMapEntry(addr, symbol);
                }
            }
            entries.Sort();
            // dump the map
            //for (int i = 0; i < entries.Count; i++) {
            //  Entry e = (Entry) entries[i];
            //  Console.WriteLine("{0} {1:x} {2}", i, e.addr, e.symbol);
            //}
            //
            Console.WriteLine(" Okay");
        }

        static void ProcessLog()
        {
            Console.Write("Processing log ");

            int counter = 0;

            while (true) {
                String line = logStream.ReadLine();
                // End of file?
                if (line == null) {
                    break;
                }

                // We need the comment line that provides the load address bias for our symbols.
                // This is always in the first couple of lines of the log and is currently the
                // only 'z' (comment) entry.
                if (loadBias == 0 &&
                    line.Length > 30 &&
                    line[0] == 'z' &&
                    line.IndexOf("CLRProfiler_WriteHeader") > 0) {
                    string eipString = line.Substring(4, line.IndexOf(" ", 4)-4);
                    ulong eip = ulong.Parse(eipString, NumberStyles.HexNumber);
                    ulong addr = FindWriteHeader();

                    // round down to a page, discarding any noise in our calculation due to the
                    // method prolog
                    loadBias = (eip - addr) & ~(ulong)0xfff;
                    Console.WriteLine("Deducing .text segment was loaded at {0:x}", loadBias);
                }

                // Process any function entries, replacing process eip values with symbolic values.
                if (line.Length > 30 && line[0] == 'f') {
                    int iStart = line.IndexOf("Function_EIP_0x");
                    if (iStart > 0) {
                        int iEnd = line.IndexOf(" (UNKNOWN ARGUMENTS) ", iStart);
                        if (iEnd > 0) {
                            string eipString = line.Substring(iStart + 15, iEnd - iStart - 15);
                            ulong eip = ulong.Parse(eipString, NumberStyles.HexNumber);
                            Entry e = FindEntry(eip);
                            ulong adjustEip = e.addr + loadBias;

                            // Recompose a new line with the symbol and the EIP for the start
                            // of that symbol, rather than the EIP of the stack trace.
                            line = line.Substring(0, iStart) +
                                   e.symbol +
                                   " (UNKNOWN ARGUMENTS) 0x" +
                                   adjustEip.ToString("x") +
                                   " 1 ";
                        }
                    }
                }
                newStream.WriteLine(line);
                if ((counter++ % 1000) == 0)
                    Console.Write("*");
            }
            newStream.Close();
            Console.WriteLine(" Okay");
        }

        static void Main(string[] args)
        {
            if (args.Length != 2) {
                Console.WriteLine("Usage: ProfMap <log> <map>");
                return;
            }

            string logName = args[0];
            string mapName = args[1];

            if (!File.Exists(logName)) {
                Console.WriteLine("Cannot find log file {0}", logName);
                return;
            }
            logStream = new StreamReader(logName);

            if (!File.Exists(mapName)) {
                Console.WriteLine("Cannot find map file {1}", mapName);
                return;
            }
            mapStream = new StreamReader(mapName);

            string newName = logName + "new";
            newStream = new StreamWriter(newName);

            Console.WriteLine("Old log: {0}, map: {1}, creating new log {2}",
                              logName, mapName, newName);

            entries = new ArrayList();

            ReadMap();
            ProcessLog();

            Console.WriteLine("Done");
        }
    }
}
