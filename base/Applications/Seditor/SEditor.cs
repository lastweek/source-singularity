// ----------------------------------------------------------------------------
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
// ----------------------------------------------------------------------------

using DirectoryService.Utils;
using FileSystem.Utils;
using System;
using System.Collections;
using System.Text;
using System.Text.RegularExpressions;
using System.ParseNumbers;

using Microsoft.Singularity;
using System.IO;

using System.GC;
using System.Runtime.Remoting;
using System.Runtime.InteropServices;
using System.Runtime.CompilerServices;
using System.Threading;
using System.Diagnostics;

using Microsoft.SingSharp;
using Microsoft.Singularity.Directory;
using Microsoft.Singularity.V1.Services;
using Microsoft.Singularity.Io;
using Microsoft.Singularity.FileSystem;
using Microsoft.Singularity.Channels;

using Microsoft.Contracts;
using Microsoft.SingSharp.Reflection;
using Microsoft.Singularity.Applications;
using Microsoft.Singularity.Configuration;
[assembly: Transform(typeof(ApplicationResourceTransform))]

namespace Microsoft.Singularity.Applications 
{
    [ConsoleCategory(HelpMessage="Stream Editor", DefaultAction=true)]
    internal class Parameters {
        [InputEndpoint("data")]
        public readonly TRef<UnicodePipeContract.Exp:READY> Stdin;

        [OutputEndpoint("data")]
        public readonly TRef<UnicodePipeContract.Imp:READY> Stdout;

        [StringParameter( "filename", Mandatory=true, Position=0, HelpMessage="Name of file.")]
        internal string fileName;

        reflective internal Parameters();

        internal int AppMain() {
             SEditor.AppMain(this);
             return 0;
        }
    }
    public class SEditor
    {
        internal static void AppMain(Parameters! config)
        {
            // constants
            string EditorName = "SEditor";
            int szLineCount = 0;
            int nIndex = 0;

            //FOR DEBUG
            // Console.WriteLine("Number of cmd line params = {0}", args.Length);
            
            // FOR DEBUG
            // Console.WriteLine("args[1] is {0}", args[1]);
            string filename = config.fileName;

            string szSrcLine;
            ArrayList szContents = new ArrayList();

            if (File.Exists(filename)) {
                FileStream fsInput = new FileStream(filename, FileMode.Open, FileAccess.Read);
                StreamReader srInput = new StreamReader(fsInput);
                while ((szSrcLine = srInput.ReadLine()) != null) {
                    szContents.Add(szSrcLine);
                    // FOR DEBUG
                    // Console.WriteLine("{0}", szSrcLine);
                    // Console.ReadLine();
                    // END DEBUG
                }
                srInput.Close();
                fsInput.Close();

                // Display number of lines loaded
                szLineCount = szContents.Count;
                Console.WriteLine("* Number of lines read from {0} was {1}", filename, szLineCount);

                // FOR DEBUG ONLY: display contents of file
                // for (nIndex = 0; nIndex < szContents.Count; nIndex++) {
                // write line to console with numbering
                //    Console.WriteLine("{0}: {1}", (nIndex + 1), szContents[nIndex]);
                // }
            }
            else if (System.IO.Directory.Exists(filename)) { // check that it's not a directory
                Console.WriteLine("Exiting: {0} is a directory.", filename);
                Console.WriteLine("Syntax: {0} filename", EditorName);
                return;
            }
            else { // not a directory, but file doesn't exist, so create it
                Console.WriteLine("* Creating new file.");
            }

            // Command parser - this is the main program loop
            Parser(szContents, nIndex, filename);
        } // end Main


        // Parse incoming commands
        static void Parser(ArrayList szArray, int pIndex, string InputFileName)
        {
            //FOR DEBUG
            // Console.WriteLine("* Parser called.");
            // Console.WriteLine("* Current line index is {0}," pIndex);
            Console.Write("* ");
            string ParserInput;
            string ParserInputFirstChar;
            string BackupFileName = "";
            int tempIndex = 0;
            ArrayList tempArray = new ArrayList();
            bool IsTextUpdated = false;
            int tempSize = 0;

            // build proper backup file name - look for extension if it exists, and replace it with (or add to) ".bak"
            if (Path.HasExtension(InputFileName) && (Path.GetExtension(InputFileName) != ".bak")) { // has an extension other than .bak
                BackupFileName = Path.ChangeExtension(InputFileName, ".bak");
            }
            else if (Path.HasExtension(InputFileName) && (Path.GetExtension(InputFileName) == ".bak")) { // .bak already in use, use something else
                Console.WriteLine("{0} ends in .bak - using .ba2 for backup files...", InputFileName);
                Console.Write("* ");
                BackupFileName = Path.ChangeExtension(InputFileName, ".ba2");
            }
            else { // no extension, so add one
                BackupFileName = InputFileName + ".bak";
            }

            while (((ParserInput = GetConsoleInput()) != "q") && (ParserInput != "Q") && (ParserInput != null)) {
                if (ParserInput != "") {
                    //FOR DEBUG
                    //Console.WriteLine("* Input was {0}", ParserInput);
                    //Console.Write("* ");

                    // ParserInputFirstChar = Convert.ToString(ParserInput[0]);
                    ParserInputFirstChar = ParserInput[0].ToString();
                }
                else {
                    Console.Write("* ");
                    continue;
                }

                // Simple switch based parsing of commands
                switch (ParserInputFirstChar) {
                    case "h":
                    case "H":
                    case "?":
                        Console.WriteLine("* Commands available are:");
                        Console.WriteLine("*   ?, (h | H) - prints this message");
                        Console.WriteLine("*   [number] - start editing at line [number]");
                        Console.WriteLine("*   (a | A) - append lines at end of file");
                        Console.WriteLine("*   (c | C)[num1],[num2],[destnum] - copy lines from num1 to num2 to dest num");
                        Console.WriteLine("*   (d | D); (d | D)[num]; (d | D)[num1],[num2] - delete current line, ");
                        Console.WriteLine("*      line at num, lines from num1 to num2");
                        Console.WriteLine("*   (e | E) - exit, saving changes");
                        Console.WriteLine("*   (i | I); (i | I)[num] - insert line above current line, or above line num");
                        Console.WriteLine("*   (l | L); (l | L)[num]; (l | L)[num1],[num2] - list the whole file, ");
                        Console.WriteLine("*      list the line at num, list the lines from num1 to num2");
                        Console.WriteLine("*   (m | M)[num1],[num2],[destnum] - move lines from num1 to num2 to dest num");
                        Console.WriteLine("*   (n | N) - print current line number (location in file)");
                        Console.WriteLine("*   (p | P) - same as l, only displays one page at a time.");
                        Console.WriteLine("*   (q | Q) - quit, saving no changes since last write");
                        Console.WriteLine("*   (r | R)[num1],([num2] | ?),[searchstr]^[replacestr] - replace");
                        Console.WriteLine("*      searchstr with replacestr. If ? is used as second param, sub is prompted");
                        Console.WriteLine("*   (s | S)[num1],([num2] | ?),[searchstr] - search for searchstr. ");
                        Console.WriteLine("*      If ? is used as second param, occurrence is displayed with prompt");
                        Console.WriteLine("*      until accepted with y, Y, or newline.");
                        Console.WriteLine("*   (t | T)[num],[filename] - insert contents of filename above line num.");
                        Console.WriteLine("*   (w | W) - write contents of memory to filename. Original contents will be");
                        Console.WriteLine("*      backed up as for exit command.");
                        break;
                    case "a":
                    case "A":
                        // FOR DEBUG
                        // Console.WriteLine("* Input was for AppendAtEOF()");

                        tempSize = szArray.Count;

                        tempArray = AppendAtEOF(szArray);

                        if (tempArray.Count > tempSize) { // array has grown, so assume text modified
                            IsTextUpdated = true;
                        }

                        szArray = tempArray;
                        pIndex = tempArray.Count;       // move line pointer to the end of the file

                        break;
                    case "c":
                    case "C":
                        // FOR DEBUG
                        // Console.WriteLine("* Input was for CopyLines()");
                        if (szArray.Count == 0) {
                            Console.WriteLine("* No text available to copy - new empty file");
                        }
                        else {
                            tempArray = CopyLines(szArray, ParserInput, pIndex);

                            if (szArray.Count != pIndex) { // assume the array has changed, ergo text modified
                                IsTextUpdated = true;
                            }

                            szArray = tempArray;
                        }

                        break;
                    case "d":
                    case "D":
                        // FOR DEBUG
                        // Console.WriteLine("* Input was for DeleteLines()");
                        if (szArray.Count == 0) {
                            Console.WriteLine("* No text available to delete - new empty file");
                        }
                        else {
                            tempArray = DeleteLines(szArray, ParserInput, pIndex);

                            if (szArray.Count != pIndex) { // assume the array has changed, ergo text modified
                                IsTextUpdated = true;
                            }

                            szArray = tempArray;

                            tempIndex = szArray.Count;

                            if (tempIndex < pIndex) { // deletion has reduced line count below pIndex - reset the pointer
                                pIndex = tempIndex;
                            }
                        }

                        break;
                    case "e":
                    case "E":
                        // FOR DEBUG
                        // Console.WriteLine("* Input was for Exit ...");

                        if (szArray.Count == 0) {
                            Console.WriteLine("* No text to save, exiting without write.");
                            return;
                        }
                        else {
                            Console.WriteLine("* Exiting....");
                            EditorWrite(szArray, InputFileName, BackupFileName);
                            return;
                        }

                        break;
                    case "i":
                    case "I":
                        // FOR DEBUG
                        // Console.WriteLine("* Input was for InsertAtLine()");

                        // Insert is a special case. The line pointer for the file needs to move
                        // to the point of insertion if an argument is given, so we will parse that
                        // here and pass the results, since we need to get the updated array back.

                        if (szArray.Count == 0) {
                            Console.WriteLine("* No lines to insert above - new empty file");
                        }
                        else {
                            Regex shortr = new Regex(@"^[iI](?<1>\d+)", RegexOptions.Compiled);
                            Match shortm;
                            shortm = shortr.Match(ParserInput);
                            Group shortg1 = shortm.Groups[1];

                            if ((ParserInput == "i") || (ParserInput == "i")) {  //insert above current line pointer pIndex
                                InsertAtLine(szArray, pIndex);
                                IsTextUpdated = true;
                            }
                            else if (shortm.Success) { // we have one line number
                                //FOR DEBUG
                                //Console.WriteLine("Line number {0}", shortm.Groups[1]);

                                // write out line
                                Capture shortc1 = shortg1.Captures[0];

                                // tempIndex = Convert.ToInt32(shortc1.Value);
                                tempIndex = Int32.Parse(shortc1.Value);
                                if (tempIndex >= 1 && tempIndex <= szArray.Count) { // check for line numbers in range of file
                                    pIndex = tempIndex; // update pIndex
                                    InsertAtLine(szArray, pIndex);
                                    IsTextUpdated = true;
                                }
                                else {
                                    Console.WriteLine("* Line number {0} out of range. File length is {1}", tempIndex, szArray.Count);
                                }

                            }
                            else {
                                Console.WriteLine("Invalid match");
                            }
                        }
                        break;
                    case "l":
                    case "L":
                        // FOR DEBUG
                        //Console.WriteLine("* Input was for ListText()");

                        tempIndex = ListText(szArray, ParserInput, pIndex);
                        if (tempIndex != -1) { // update current line number if list command moved the pointer
                            pIndex = tempIndex;
                        }
                        break;
                    case "m":
                    case "M":
                        //FOR DEBUG
                        //Console.WriteLine("* Input was for MoveLines()");

                        if (szArray.Count == 0) {
                            Console.WriteLine("* No text available to move - new empty file");
                        }
                        else {
                            tempArray = MoveLines(szArray, ParserInput, pIndex);

                            szArray = tempArray;

                            IsTextUpdated = true;
                        }
                        break;
                    case "n":
                    case "N":
                        //FOR DEBUG
                        // Console.WriteLine("* Input was for PrintLineNumber()");

                        Console.WriteLine("* {0}", pIndex);
                        break;
                    case "p":
                    case "P":
                        // FOR DEBUG
                        // Console.WriteLine("* Input was for PageText()");

                        tempIndex = PageText(szArray, ParserInput, pIndex);
                        if (tempIndex != -1) { // update current line number if list command moved the pointer
                            pIndex = tempIndex;
                        }

                        break;
                    case "r":
                    case "R":
                        //FOR DEBUG
                        // Console.WriteLine("* Input was for ReplaceText()");

                        if (szArray.Count == 0) {
                            Console.WriteLine("* No text available to replace");
                        }
                        else {
                            tempArray = ReplaceText(szArray, ParserInput, pIndex);
                            szArray = tempArray;
                            IsTextUpdated = true;
                        }
                        break;
                    case "s":
                    case "S":
                        //FOR DEBUG
                        // Console.WriteLine("* Input was for SearchForText()");

                        if (szArray.Count == 0) {
                            Console.WriteLine("* No text available to search");
                        }
                        else {
                            tempIndex = SearchForText(szArray, ParserInput, pIndex);
                            if (tempIndex != -1) { // update current line number if list command moved the pointer
                                pIndex = tempIndex;
                            }
                        }
                        break;
                    case "t":
                    case "T":
                        // FOR DEBUG
                        // Console.WriteLine("* Input was for TransferText()");

                        tempArray = TransferText(szArray, ParserInput);

                        if (szArray.Count != pIndex) { // assume the array has changed, ergo text modified
                            IsTextUpdated = true;
                        }

                        szArray = tempArray;

                        break;
                    case "w":
                    case "W":
                        // FOR DEBUG
                        // Console.WriteLine("* Input was for WriteTextToFile()");

                        if (szArray.Count == 0) {
                            Console.WriteLine("* No text to save.");
                        }
                        else {
                            EditorWrite(szArray, InputFileName, BackupFileName);
                            IsTextUpdated = false;
                        }

                        break;
                    case "":
                        break;
                    default:
                        int LineNumber = 0;

                        if (szArray.Count == 0) {
                            Console.WriteLine("* No lines to edit at - new empty file");
                            break;
                        }
                        else {

                            try {
                                // LineNumber = Convert.ToInt32(ParserInput);
                                LineNumber = Int32.Parse(ParserInput);
                            }
                            catch (System.ArgumentNullException) {
                                Console.WriteLine("String is null.");
                                break;
                            }
                            catch (System.FormatException) {
                                Console.WriteLine("* Unrecognized command");
                                break;
                            }
                            catch (System.OverflowException) {
                                Console.WriteLine("* Overflow in string to int conversion.");
                                break;
                            }
                        }

                        //FOR DEBUG
                        // Console.WriteLine("* Input was for EditAtLine() - line {0}", LineNumber);

                        // update line pointer to LineNumber
                        pIndex = LineNumber;

                        tempArray = EditAtLine(szArray, pIndex);

                        szArray = tempArray;

                        IsTextUpdated = true;

                        break;
                }
                Console.Write("* ");
            }
            if (IsTextUpdated == true) { // ask them if they really wanted to quit without writing text out
                Console.WriteLine("* WARNING: modified text not saved.");
                Console.Write("* Save? (Y/N) ");

                string SaveReply = GetConsoleInput();
                // string SaveReplyFirstChar = Convert.ToString(SaveReply[0]);
                if (SaveReply != "") {
                    string SaveReplyFirstChar = SaveReply[0].ToString();
                    switch (SaveReplyFirstChar) {
                        case "y":
                        case "Y":
                            Console.WriteLine("* Exiting....");
                            EditorWrite(szArray, InputFileName, BackupFileName);
                            break;
                        default:
                            Console.WriteLine("* Exiting without save.");
                            break;
                    }
                }
                else {
                    Console.WriteLine("* Exiting without save.");
                }
            }

        } // end of Parser


        // ListText - returns updated list pointer as int
        static int ListText(ArrayList szArray, string ParserInput, int nIndex)
        {
            Regex fullr = new Regex(@"^[lL](?<1>\d+),(?<2>\d+)", RegexOptions.Compiled);
            Regex shortr = new Regex(@"^[lL](?<1>\d+)", RegexOptions.Compiled);
            Match fullm;
            Match shortm;
            int listSuccess = 0;
            int PAGEWIDTH = 72;  // allow for line numbers in printouts - up to 99,999.
                                 // TODO: adjust line number range dynamically for large files
            int tempwidth = 0;
            string workstring = "";
            string tempstring = "";
            int remainder = 0;
            int division = 0;
            int linesinline = 0;
            int leftinstring = 0;
            int lowLine = 0;
            int hiLine = 0;

            //FOR DEBUGGING
            //Console.WriteLine("Current line number is {0}", nIndex);

            fullm = fullr.Match(ParserInput);
            shortm = shortr.Match(ParserInput);
            Group fullg1 = fullm.Groups[1];
            Group fullg2 = fullm.Groups[2];
            Group shortg1 = shortm.Groups[1];

            if (fullm.Success) { // we think we have two line numbers, set lowLine and hiLine accordingly

                //FOR DEBUG
                //Console.WriteLine("First line number {0}, last line number {1}", fullm.Groups[1], fullm.Groups[2]);

                Capture fullc1 = fullg1.Captures[0];
                Capture fullc2 = fullg2.Captures[0];

                // int lowLine = Convert.ToInt32(fullc1.Value);
                lowLine = Int32.Parse(fullc1.Value) - 1; // offset by one to allow for difference in starting point...

                // int hiLine = Convert.ToInt32(fullc2.Value);
                hiLine = Int32.Parse(fullc2.Value);     // but leave this one alone, due to the loop

                // test for numbers out of range or out of order
                if ((lowLine <= hiLine) && (lowLine >= 0 && lowLine <= szArray.Count) && (hiLine >= 0 && hiLine <= szArray.Count)) {
                // continue on to listing...
                }
                else { // bad arguments
                    Console.WriteLine("* Malformed arguments to list, or line out of range.");
                    Console.WriteLine("*   lnum1,num2 where num1 <= num2 and num2 <= length of file.");
                    Console.WriteLine("*   File length is {0}.", szArray.Count);
                    listSuccess = -1;
                    return listSuccess;
                }
            }
            else if (shortm.Success) { // we have one line number
                //FOR DEBUG
                //Console.WriteLine("Line number {0}", shortm.Groups[1]);

                // write out line
                Capture shortc1 = shortg1.Captures[0];

                // nIndex = Convert.ToInt32(shortc1.Value);
                nIndex = Int32.Parse(shortc1.Value);

                if (nIndex >= 1 && nIndex <= szArray.Count) { // check for line numbers in range of file
                    lowLine = nIndex - 1;
                    hiLine = nIndex;
                    // proceed to listing
                }
                else {
                    Console.WriteLine("* Line number {0} out of range. File length is {1}", nIndex, szArray.Count);
                    listSuccess = -1;
                    return listSuccess;
                }
            }
            else if ((ParserInput == "l") || (ParserInput == "L")) {  // set lowLine = 0, hiLine = szArray.Count
                lowLine = 0;
                hiLine = szArray.Count;
            }
            else {
                Console.WriteLine("Invalid match");
                listSuccess = -1;
                return listSuccess;
            }

            // print out buffer contents between lowLine and hiLine
            for (nIndex = lowLine; nIndex < hiLine; nIndex++) {
                workstring = szArray[nIndex].ToString();
                tempwidth = workstring.Length;
                if (tempwidth > PAGEWIDTH) {
                    //FOR DEBUG
                    //Console.WriteLine(" need to break up line length");
                    while (division != 1) {
                        linesinline++;
                        division = tempwidth / PAGEWIDTH;
                        remainder = tempwidth % PAGEWIDTH;
                        tempwidth = tempwidth - PAGEWIDTH;
                        //FOR DEBUG
                        //Console.WriteLine("remainder = {0}, division = {1}, tempwidth = {2}, linesinline = {3}", remainder, division, tempwidth, linesinline);
                        //Console.ReadLine();
                    }
                    if (remainder != 0) {
                        linesinline++;
                        //FOR DEBUG
                        //Console.WriteLine("remainder = {0}, division = {1}, tempwidth = {2}, linesinline = {3}", remainder, division, tempwidth, linesinline);
                        //Console.ReadLine();
                    }
                    leftinstring = workstring.Length;
                    while (linesinline > 0) {
                        if (leftinstring >= PAGEWIDTH) {
                            tempstring = workstring.Substring(workstring.Length - leftinstring, PAGEWIDTH);
                        }
                        else {
                            tempstring = workstring.Substring(workstring.Length - leftinstring, remainder);
                        }
                        Console.WriteLine("{0,5}: {1}", (nIndex + 1), tempstring);
                        linesinline--;
                        if (leftinstring > PAGEWIDTH) {
                            leftinstring = leftinstring - PAGEWIDTH;
                        }
                    }

                    // rezero worker constants
                    remainder = 0;
                    division = 0;
                    linesinline = 0;
                    leftinstring = 0;
                    listSuccess = 1;
                }
                else {
                    Console.WriteLine("{0,5}: {1}", (nIndex + 1), szArray[nIndex]);
                }

                listSuccess = 1;
            }

            if (listSuccess == 1) {
               return nIndex; // paging worked
            }
            else {            // note: you should never get here 
               return -1;     // bad arguments, don't move line pointer
            }
        } // end of ListText

        // CopyLines() - returns updated ArrayList with copies done, or the original ArrayList
        static ArrayList CopyLines(ArrayList szArray, string ParserInput, int nIndex)
        {
            Queue copyQueue = new Queue();
            Regex copyr = new Regex(@"^[cC](?<1>\d+),(?<2>\d+),(?<3>\d+)", RegexOptions.Compiled);
            Match copym;

            //FOR DEBUGGING
            //Console.WriteLine("Current line number is {0}", nIndex);

            copym = copyr.Match(ParserInput);
            Group copyg1 = copym.Groups[1];
            Group copyg2 = copym.Groups[2];
            Group copyg3 = copym.Groups[3];

            if (copym.Success) { // we think we have two line numbers and a dest number
                //FOR DEBUG
                //Console.WriteLine("First line number {0}, last line number {1}, dest {2}", copym.Groups[1], copym.Groups[2], copym.Groups[3]);

                //Put array elements to be copied into copyQueue
                Capture copyc1 = copyg1.Captures[0]; // first line of copy
                Capture copyc2 = copyg2.Captures[0]; // last line of copy

                // int lowLine = Convert.ToInt32(copyc1.Value);
                int lowLine = Int32.Parse(copyc1.Value);

                // int hiLine = Convert.ToInt32(copyc2.Value);
                int hiLine = Int32.Parse(copyc2.Value);

                // test for numbers out of range or out of order
                if ((lowLine <= hiLine) && (lowLine >= 1 && lowLine <= szArray.Count) && (hiLine >= 1 && hiLine <= szArray.Count)) {
                    for (nIndex = lowLine; nIndex <= hiLine; nIndex++) {
                        //FOR DEBUG
                        // Console.WriteLine("{0}: {1}", nIndex, szArray[nIndex - 1]);

                        copyQueue.Enqueue(szArray[nIndex - 1]);
                    }

                    // check dest num valid
                    Capture copyc3 = copyg3.Captures[0];

                    // int destLine = Convert.ToInt32(copyc3.Value);
                    int destLine = Int32.Parse(copyc3.Value);

                    if (destLine >= 1 && destLine <= szArray.Count) {
                        // insert copyQueue at point dest in szArray
                        // note that due to the indexing offset you need to decrement destLine by 1 here
                        szArray.InsertRange(destLine - 1, copyQueue);
                    }
                    else if (destLine > szArray.Count) { // ask them if they want the copy at the end of the file
                        Console.Write("* Copy past end of file - do you want block appended? (y/n) ");
                        string appendReply = GetConsoleInput();
                        // string appendReplyFirstChar = Convert.ToString(appendReply[0]);
                        if (appendReply != "") {
                            string appendReplyFirstChar = appendReply[0].ToString();
                            switch (appendReplyFirstChar) {
                                case "y":
                                case "Y":
                                    szArray.AddRange(copyQueue);
                                    break;
                                default:
                                    Console.WriteLine("* Aborting copy.");
                                    break;
                            }
                        }
                        else {
                            Console.WriteLine("* Aborting copy.");
                        }
                     }
                     else {
                        Console.WriteLine("* Invalid copy destination.");
                        Console.WriteLine("*   cnum1,num2,dest where num1 <= num2, num2 and dest <= length of file.");
                        Console.WriteLine("*   File length is {0}.", szArray.Count);
                     }
                }
                else { // bad arguments
                    Console.WriteLine("* Malformed arguments to copy, or line out of range.");
                    Console.WriteLine("*   cnum1,num2 where num1 <= num2, num2 and dest <= length of file.");
                    Console.WriteLine("*   File length is {0}.", szArray.Count);
                }

              return szArray; // c[num1,num2,dest] worked
            }
            else {
                Console.WriteLine("Invalid match");
                return szArray;
            }
        } // end of CopyLines

        // DeleteLines() - returns updated ArrayList with deletes done, or the original ArrayList
        static ArrayList DeleteLines(ArrayList szArray, string ParserInput, int nIndex)
        {
            Regex fullr = new Regex(@"^[dD](?<1>\d+),(?<2>\d+)", RegexOptions.Compiled);
            Regex shortr = new Regex(@"^[dD](?<1>\d+)", RegexOptions.Compiled);
            Match fullm;
            Match shortm;

            //FOR DEBUGGING
            //Console.WriteLine("Current line number is {0}", nIndex);

            fullm = fullr.Match(ParserInput);
            shortm = shortr.Match(ParserInput);
            Group fullg1 = fullm.Groups[1];
            Group fullg2 = fullm.Groups[2];
            Group shortg1 = shortm.Groups[1];

            if ((ParserInput == "d") || (ParserInput == "D")) {  // delete line at current nIndex (which means subtracting 1)
                szArray.RemoveAt(nIndex - 1);

                return szArray;
            }
            else if (fullm.Success) { // we think we have two line numbers
                //FOR DEBUG
                //Console.WriteLine("First line number {0}, last line number {1}", fullm.Groups[1], fullm.Groups[2]);

                //delete lines between first and second numbers
                Capture fullc1 = fullg1.Captures[0];
                Capture fullc2 = fullg2.Captures[0];

                // int lowLine = Convert.ToInt32(fullc1.Value);
                int lowLine = Int32.Parse(fullc1.Value);

                // int hiLine = Convert.ToInt32(fullc2.Value);
                int hiLine = Int32.Parse(fullc2.Value);

                // test for numbers out of range or out of order
                if ((lowLine <= hiLine) && (lowLine >= 1 && lowLine <= szArray.Count) && (hiLine >= 1 && hiLine <= szArray.Count) && ((hiLine - lowLine) != 0)) {
                    szArray.RemoveRange(lowLine - 1, ((hiLine - lowLine) + 1));
                }
                else { // bad arguments
                    Console.WriteLine("* Malformed arguments to list, or line out of range.");
                    Console.WriteLine("*   dnum1,num2 where num1 <= num2 and num2 <= length of file.");
                    Console.WriteLine("*   File length is {0}.", szArray.Count);
                }
                return szArray; // end of d[num1,num]
            }
            else if (shortm.Success) { // we have one line number
                //FOR DEBUG
                //Console.WriteLine("Line number {0}", shortm.Groups[1]);

                // delete line
                Capture shortc1 = shortg1.Captures[0];

                // nIndex = Convert.ToInt32(shortc1.Value);
                nIndex = Int32.Parse(shortc1.Value);

                if (nIndex >= 1 && nIndex <= szArray.Count) { // check for line numbers in range of file
                    szArray.RemoveAt(nIndex - 1);
                }
                else {
                    Console.WriteLine("* Line number {0} out of range. File length is {1}", nIndex, szArray.Count);
                    return szArray;
                }
                return szArray;
            }
            else {
                Console.WriteLine("Invalid match");
                return szArray;
            }
        } // end of DeleteLines

        // EditAtLine() - edit the line at nIndex in szArray. Since we know the line number, we don't have
        //                to parse ParserInput here.
        static ArrayList EditAtLine(ArrayList szArray, int nIndex)
        {
            Queue editQueue = new Queue();

            if (nIndex >= 1 && nIndex <= szArray.Count) { // check that line number is in range of file
                Console.WriteLine("{0}: {1}", nIndex, szArray[nIndex - 1]);
                Console.Write("> ");
                string editInput = GetConsoleInput();
                if (editInput == "") {
                    return szArray;
                }
                else {
                    editQueue.Enqueue(editInput);
                    szArray.RemoveAt(nIndex - 1);
                    szArray.InsertRange(nIndex - 1, editQueue);
                }
            }
            else {
                Console.WriteLine("* Line number {0} out of range. File length is {1}", nIndex, szArray.Count);
            }
            return szArray;
        } // end of EditAtLine


        // InsertAtLine() - insert line(s) above nIndex in szArray. Since we know the line number, we don't have
        //                to parse ParserInput here.
        static ArrayList InsertAtLine(ArrayList szArray, int nIndex)
        {
            Queue insertQueue = new Queue();
            string insertInput = null;

            Console.WriteLine("* Inserting text above {0}: {1}", nIndex, szArray[nIndex - 1]);
            Console.WriteLine("* Press ^^ to end input.");

            while (insertInput != "^^") { // Double carat ^^ ends input - would have used control char, but need tty to understand them....
                Console.Write("> ");
                insertInput = GetConsoleInput();
                if (insertInput != "^^") {
                    insertQueue.Enqueue(insertInput);
                }
            }
            szArray.InsertRange(nIndex - 1, insertQueue);
            return szArray;
        } // end of InsertAtLine

        // AppendAtEOF() - append line(s) below current end of szArray. Since we are appending, we don't have
        //                to parse ParserInput here.
        static ArrayList AppendAtEOF(ArrayList szArray)
        {
            Queue appendQueue = new Queue();
            string appendInput = null;

            Console.WriteLine("* Appending text at EOF - Press ^^ to end input.");

            while (appendInput != "^^") { // ^^ ends input
                Console.Write("> ");
                appendInput = GetConsoleInput();
                if (appendInput != "^^") {
                    appendQueue.Enqueue(appendInput);
                }
            }
            szArray.AddRange(appendQueue);
            return szArray;
        } // end of AppendAtEOF()

        // MoveLines() - returns updated ArrayList with moves done, or the original ArrayList
        static ArrayList MoveLines(ArrayList szArray, string ParserInput, int nIndex)
        {
            Queue moveQueue = new Queue();
            Regex mover = new Regex(@"^[mM](?<1>\d+),(?<2>\d+),(?<3>\d+)", RegexOptions.Compiled);
            Match movem;

            //FOR DEBUGGING
            //Console.WriteLine("Current line number is {0}", nIndex);

            movem = mover.Match(ParserInput);
            Group moveg1 = movem.Groups[1];
            Group moveg2 = movem.Groups[2];
            Group moveg3 = movem.Groups[3];

            if (movem.Success) { // we think we have two line numbers and a dest number
                //FOR DEBUG
                // Console.WriteLine("First line number {0}, last line number {1}, dest {2}", movem.Groups[1], movem.Groups[2], movem.Groups[3]);

                //Put array elements to be moved into moveQueue
                Capture movec1 = moveg1.Captures[0]; // first line of move
                Capture movec2 = moveg2.Captures[0]; // last line of move

                // int lowLine = Convert.ToInt32(movec1.Value);
                int lowLine = Int32.Parse(movec1.Value);

                // int hiLine = Convert.ToInt32(movec2.Value);
                int hiLine = Int32.Parse(movec2.Value);

                // test for numbers out of range or out of order
                if ((lowLine <= hiLine) && (lowLine >= 1 && lowLine <= szArray.Count) && (hiLine >= 1 && hiLine <= szArray.Count)) {
                    for (nIndex = lowLine; nIndex <= hiLine; nIndex++) {
                        //FOR DEBUG
                        // Console.WriteLine("{0}: {1}", nIndex, szArray[nIndex - 1]);

                        moveQueue.Enqueue(szArray[nIndex - 1]);
                    }

                    // check dest num valid
                    // However, you can't overlap - dest must either be before the block you're moving, or after it.
                    Capture movec3 = moveg3.Captures[0];

                    // int destLine = Convert.ToInt32(movec3.Value);
                    int destLine = Int32.Parse(movec3.Value);

                    if ((destLine >= 1 && destLine <= szArray.Count) && ((destLine < lowLine) || (destLine) > hiLine)) {
                        // insert moveQueue at point dest in szArray
                        // note that due to the indexing offset you need to decrement destLine by 1 here
                        szArray.InsertRange(destLine - 1, moveQueue);

                        // once the insertion is complete, then you can delete the lines from the original
                        // however, need to be careful about seeing what happened to the original lines - they
                        // may have moved their indexes in the array depending on where you did the insertion
                        if (destLine > hiLine) { // indexes stayed the same for the original block - delete it
                            szArray.RemoveRange(lowLine - 1, ((hiLine - lowLine) + 1));
                        }
                        else { // destLine above lowLine, need to adjust
                            int padLine = hiLine - lowLine;
                            szArray.RemoveRange((lowLine + padLine), ((hiLine - lowLine) + 1));
                        }
                    }
                    else if (destLine > szArray.Count) { // ask them if they want the move at the end of the file
                        Console.Write("* Move past end of file - do you want block appended? (y/n) ");
                        string appendReply = GetConsoleInput();
                        // string appendReplyFirstChar = Convert.ToString(appendReply[0]);
                        if (appendReply != "") {
                            string appendReplyFirstChar = appendReply[0].ToString();
                            switch (appendReplyFirstChar) {
                                case "y":
                                case "Y":
                                    szArray.AddRange(moveQueue);
                                    // we don't have to worry about the index adjustment here - we can just remove the lines
                                    // from their original location
                                    szArray.RemoveRange(lowLine - 1, ((hiLine - lowLine) + 1));
                                    break;
                                default:
                                    Console.WriteLine("* Aborting move.");
                                    break;
                            }
                        }
                        else {
                            Console.WriteLine("* Aborting move.");
                        }
                   }
                   else {
                        Console.WriteLine("* Invalid move destination.");
                        Console.WriteLine("*   mnum1,num2,dest where num1 <= num2, num2 and dest <= length of file,");
                        Console.WriteLine("*   but dest not within num1 - num2 range.");
                        Console.WriteLine("*   File length is {0}.", szArray.Count);
                   }
                }
                else { // bad arguments
                    Console.WriteLine("* Malformed arguments to move, or line out of range.");
                    Console.WriteLine("*   mnum1,num2 where num1 <= num2, num2 and dest <= length of file,");
                    Console.WriteLine("*   but dest not within num1 - num2 range.");
                    Console.WriteLine("*   File length is {0}.", szArray.Count);
                }
                return szArray; // m[num1,num2,dest] worked
            }
            else {
                Console.WriteLine("Invalid match");
                return szArray;
            }
        } // end of MoveLines

        // SearchForText() - returns updated list pointer, since we're not modifying any text
        static int SearchForText(ArrayList szArray, string ParserInput, int nIndex)
        {
            Regex closedsearchr = new Regex(@"^[sS](?<1>\d+),(?<2>\d+),(?<3>.+)", RegexOptions.Compiled);
            Regex opensearchr = new Regex(@"^[sS](?<1>\d+),\?,(?<2>.+)", RegexOptions.Compiled);
            Match closedsearchm;
            Match opensearchm;

            //FOR DEBUGGING
            //Console.WriteLine("Current line number is {0}", nIndex);

            closedsearchm = closedsearchr.Match(ParserInput);
            opensearchm = opensearchr.Match(ParserInput);
            Group closedsearchg1 = closedsearchm.Groups[1];
            Group closedsearchg2 = closedsearchm.Groups[2];
            Group closedsearchg3 = closedsearchm.Groups[3];
            Group opensearchg1 = opensearchm.Groups[1];
            Group opensearchg2 = opensearchm.Groups[2];
            int searchSuccess = 0;

            if (closedsearchm.Success) { // we think we have two line numbers and a search string
                //FOR DEBUG
                // Console.WriteLine("First line number {0}, last line number {1}, string {2}", closedsearchm.Groups[1], closedsearchm.Groups[2], closedsearchm.Groups[3]);

                Capture closedsearchc1 = closedsearchg1.Captures[0];
                Capture closedsearchc2 = closedsearchg2.Captures[0];
                Capture closedsearchc3 = closedsearchg3.Captures[0];

                // int lowLine = Convert.ToInt32(closedsearchc1.Value);
                int lowLine = Int32.Parse(closedsearchc1.Value);

                // int hiLine = Convert.ToInt32(closedsearchc2.Value);
                int hiLine = Int32.Parse(closedsearchc2.Value);

                Regex searchstringr = new Regex(Regex.Escape(closedsearchc3.Value));
                Match searchstringm;

                // test for numbers out of range or out of order
                if ((lowLine <= hiLine) && (lowLine >= 1 && lowLine <= szArray.Count) && (hiLine >= 1 && hiLine <= szArray.Count)) {
                    for (nIndex = lowLine; nIndex <= hiLine; nIndex++) {
                        //FOR DEBUG
                        // Console.WriteLine("{0}: {1}", nIndex, szArray[nIndex - 1]);

                        // search for the searchstring in the current line
                        // searchstringm = searchstringr.Match(Regex.Escape(Convert.ToString(szArray[nIndex - 1])));
                        searchstringm = searchstringr.Match(Regex.Escape(szArray[nIndex - 1].ToString()));
                        if (searchstringm.Success) { // found a match
                            Console.WriteLine("{0}: {1}", nIndex, szArray[nIndex - 1]);
                            searchSuccess = 1;
                            break;
                        }
                        else { // no match found
                            //FOR DEBUG
                            // Console.WriteLine("* No match found");
                            searchSuccess = -1;
                        }
                    }
                }
                else { // bad arguments
                    Console.WriteLine("* Malformed arguments to search, or line out of range.");
                    Console.WriteLine("*  snum1,[num2 | ?],string where num1 <= num2 and");
                    Console.WriteLine("*  num2 <= length of file. File length is {0}", szArray.Count);
                    searchSuccess = -1;
                }

                if (searchSuccess == 1) {
                    return nIndex;
                }
                else {
                    Console.WriteLine("* No match found");
                    return -1;
                }
            }
            else if (opensearchm.Success) { // we have a starting line number and a string
                //FOR DEBUG
                // Console.WriteLine("First line number {0}, last line number {1}, string {2}", closedsearchm.Groups[1], closedsearchm.Groups[2], closedsearchm.Groups[3]);

                Capture opensearchc1 = opensearchg1.Captures[0];
                Capture opensearchc2 = opensearchg2.Captures[0];

                // int lowLine = Convert.ToInt32(opensearchc1.Value);
                int lowLine = Int32.Parse(opensearchc1.Value);

                Regex searchstringr = new Regex(Regex.Escape(opensearchc2.Value));
                Match searchstringm;

                // test for start number out of range
                if (lowLine >= 1 && lowLine <= szArray.Count) {
                    for (nIndex = lowLine; nIndex <= szArray.Count; nIndex++) {
                        //FOR DEBUG
                        // Console.WriteLine("{0}: {1}", nIndex, szArray[nIndex - 1]);

                        // search for the searchstring in the current line
                        // searchstringm = searchstringr.Match(Regex.Escape(Convert.ToString(szArray[nIndex - 1])));
                        searchstringm = searchstringr.Match(Regex.Escape(szArray[nIndex - 1].ToString()));
                        if (searchstringm.Success) { // found a match
                            Console.WriteLine("{0}: {1}", nIndex, szArray[nIndex - 1]);
                            Console.Write("O.K.? ");
                            string searchReply = GetConsoleInput();
                            if (searchReply == "") {
                                searchSuccess = 1;
                            }
                            else {
                                // string searchReplyFirstChar = Convert.ToString(searchReply[0]);
                                string searchReplyFirstChar = searchReply[0].ToString();
                                switch (searchReplyFirstChar) {
                                    case "y":
                                    case "Y":
                                        searchSuccess = 1;
                                        break;
                                    default:
                                        searchSuccess = -1;
                                        break;
                                }
                            }
                            if (searchSuccess == 1) { // found a match, so stop looking (break from the for loop)
                                break;
                            }
                        }
                        else { // no match found
                            //FOR DEBUG
                            // Console.WriteLine("* No match found");
                            searchSuccess = -1;
                        }
                    }
                }
                else { // bad arguments
                    Console.WriteLine("* Malformed arguments to search, or line out of range.");
                    Console.WriteLine("*  snum1,[num2 | ?],string where num1 <= num2 and");
                    Console.WriteLine("*  num2 <= length of file. File length is {0}", szArray.Count);
                    searchSuccess = -1;
                }

                if (searchSuccess == 1) {
                    return nIndex;
                }
                else {
                    Console.WriteLine("* No match found");
                    return -1;
                }
            }
            else { // bad match to initial parse of command args
                Console.WriteLine("* Malformed arguments to search, or line out of range.");
                Console.WriteLine("*  snum1,[num2 | ?],string where num1 <= num2 and");
                Console.WriteLine("*  num2 <= length of file. File length is {0}", szArray.Count);
                return -1;
            }
        } // end of SearchForText

        // ReplaceText() - returns updated list pointer, since we're not modifying any text
        static ArrayList ReplaceText(ArrayList szArray, string ParserInput, int nIndex)
        {
            Regex closedreplacer = new Regex(@"^[rR](?<1>\d+),(?<2>\d+),(?<3>.+)\^(?<4>.+)", RegexOptions.Compiled);
            Regex openreplacer = new Regex(@"^[rR](?<1>\d+),\?,(?<2>.+)\^(?<3>.+)", RegexOptions.Compiled);
            Match closedreplacem;
            Match openreplacem;

            //FOR DEBUGGING
            //Console.WriteLine("Current line number is {0}", nIndex);

            closedreplacem = closedreplacer.Match(ParserInput);
            openreplacem = openreplacer.Match(ParserInput);
            Group closedreplaceg1 = closedreplacem.Groups[1];
            Group closedreplaceg2 = closedreplacem.Groups[2];
            Group closedreplaceg3 = closedreplacem.Groups[3];
            Group closedreplaceg4 = closedreplacem.Groups[4];
            Group openreplaceg1 = openreplacem.Groups[1];
            Group openreplaceg2 = openreplacem.Groups[2];
            Group openreplaceg3 = openreplacem.Groups[3];

            if (closedreplacem.Success) { // we think we have two line numbers, a search string, and a replace string
                //FOR DEBUG
                // Console.WriteLine("First line number {0}, last line number {1}, string {2}, string {3}", closedreplacem.Groups[1], closedreplacem.Groups[2], closedreplacem.Groups[3], closedreplacem.Groups[4]);

                Capture closedreplacec1 = closedreplaceg1.Captures[0];
                Capture closedreplacec2 = closedreplaceg2.Captures[0];
                Capture closedreplacec3 = closedreplaceg3.Captures[0];
                Capture closedreplacec4 = closedreplaceg4.Captures[0];

                // int lowLine = Convert.ToInt32(closedreplacec1.Value);
                int lowLine = Int32.Parse(closedreplacec1.Value);

                // int hiLine = Convert.ToInt32(closedreplacec2.Value);
                int hiLine = Int32.Parse(closedreplacec2.Value);

                Regex searchstringr = new Regex(Regex.Escape(closedreplacec3.Value));
                // Match searchstringm;
                Regex replacestringr = new Regex(Regex.Escape(closedreplacec4.Value));
                string replaceresult = null;

                // test for numbers out of range or out of order
                if ((lowLine <= hiLine) && (lowLine >= 1 && lowLine <= szArray.Count) && (hiLine >= 1 && hiLine <= szArray.Count)) {
                    for (nIndex = lowLine; nIndex <= hiLine; nIndex++) {
                        //FOR DEBUG
                        // Console.WriteLine("{0}: {1}", nIndex, szArray[nIndex - 1]);

                        // search for the searchstring in the current line and replace it with the replacement string if found
                        // replaceresult = Regex.Replace(Convert.ToString(szArray[nIndex - 1]), Convert.ToString(searchstringr), Convert.ToString(replacestringr));
                        replaceresult = Regex.Replace(szArray[nIndex - 1].ToString(), searchstringr.ToString(), replacestringr.ToString());
                        Queue replaceQueue = new Queue();
                        replaceQueue.Enqueue(replaceresult);
                        szArray.InsertRange(nIndex - 1, replaceQueue);
                        szArray.RemoveAt(nIndex);
                    }
                }
                else { // bad arguments
                    Console.WriteLine("* Malformed arguments to replace, or line out of range.");
                    Console.WriteLine("*  rnum1,[num2 | ?],string,string where num1 <= num2 and");
                    Console.WriteLine("*  num2 <= length of file. File length is {0}", szArray.Count);
                }

                return szArray;
            }
            else if (openreplacem.Success) { // we have a starting line number, a search string and a replace string
                //FOR DEBUG
                // Console.WriteLine("First line number {0}, string {1}, string {2}", openreplacem.Groups[1], openreplacem.Groups[2], openreplacem.Groups[3]);

                Capture openreplacec1 = openreplaceg1.Captures[0];
                Capture openreplacec2 = openreplaceg2.Captures[0];
                Capture openreplacec3 = openreplaceg3.Captures[0];

                // int lowLine = Convert.ToInt32(openreplacec1.Value);
                int lowLine = Int32.Parse(openreplacec1.Value);

                Regex searchstringr = new Regex(Regex.Escape(openreplacec2.Value));
                Match searchstringm;
                Regex replacestringr = new Regex(Regex.Escape(openreplacec3.Value));
                string replaceresult = null;

                // test for start number out of range
                if (lowLine >= 1 && lowLine <= szArray.Count) {
                    for (nIndex = lowLine; nIndex <= szArray.Count; nIndex++) {
                        //FOR DEBUG
                        // Console.WriteLine("{0}: {1}", nIndex, szArray[nIndex - 1]);

                        // search for the searchstring in the current line
                        // searchstringm = searchstringr.Match(Regex.Escape(Convert.ToString(szArray[nIndex - 1])));
                        searchstringm = searchstringr.Match(Regex.Escape(szArray[nIndex - 1].ToString()));
                        if (searchstringm.Success) { // found a match
                            Console.WriteLine("{0}: {1}", nIndex, szArray[nIndex - 1]);
                            Console.Write("O.K.? ");
                            string replaceReply = GetConsoleInput();
                            if (replaceReply == "") {
                                // replaceresult = Regex.Replace(Convert.ToString(szArray[nIndex - 1]), Convert.ToString(searchstringr), Convert.ToString(replacestringr));
                                replaceresult = Regex.Replace(szArray[nIndex - 1].ToString(), searchstringr.ToString(), replacestringr.ToString());
                                Queue replaceQueue = new Queue();
                                replaceQueue.Enqueue(replaceresult);
                                szArray.InsertRange(nIndex - 1, replaceQueue);
                                szArray.RemoveAt(nIndex);
                            }
                            else {
                                // string replaceReplyFirstChar = Convert.ToString(replaceReply[0]);
                                string replaceReplyFirstChar = replaceReply[0].ToString();
                                switch (replaceReplyFirstChar) {
                                    case "y":
                                    case "Y":
                                        // replaceresult = Regex.Replace(Convert.ToString(szArray[nIndex - 1]), Convert.ToString(searchstringr), Convert.ToString(replacestringr));
                                        replaceresult = Regex.Replace(szArray[nIndex - 1].ToString(), searchstringr.ToString(), replacestringr.ToString());
                                        Queue replaceQueue = new Queue();
                                        replaceQueue.Enqueue(replaceresult);
                                        szArray.InsertRange(nIndex - 1, replaceQueue);
                                        szArray.RemoveAt(nIndex);
                                        break;
                                    default:
                                        break;
                                }
                            }
                        }
                        else { // no match found
                            //FOR DEBUG
                            // Console.WriteLine("* No match found");
                        }
                    }
                }
                else { // bad arguments
                    Console.WriteLine("* Malformed arguments to replace, or line out of range.");
                    Console.WriteLine("*  rnum1,[num2 | ?],string,string where num1 <= num2 and");
                    Console.WriteLine("*  num2 <= length of file. File length is {0}", szArray.Count);
                }
                return szArray;
            }
            else { // bad match to initial parse of command args
                Console.WriteLine("* Malformed arguments to replace, or line out of range.");
                Console.WriteLine("*  rnum1,[num2 | ?],string,string where num1 <= num2 and");
                Console.WriteLine("*  num2 <= length of file. File length is {0}", szArray.Count);
                return szArray;
            }
        } // end of ReplaceText

        static void EditorWrite(ArrayList szArray, string InputFileName, string BackupFileName)
        {
            int pIndex = 0;

            // check to see if file exists at all, first - if it doesn't,
            // we have to create it, but don't have to back it up.

            if (File.Exists(InputFileName)) { // it does exist, ergo we need to back it up
                // Test to see if the backup file exists, if it does, delete it (to clear it)
                if (File.Exists(BackupFileName)) {
                    File.Delete(BackupFileName);
                }

                // Then, copy the original file to one with bak at the end
                File.Copy(InputFileName, BackupFileName, true);

                // Then delete the original file (to clear it)
                File.Delete(InputFileName);

                // Then write out the contents of the buffer to our InputFileName
                FileStream fsOutput = new FileStream(InputFileName, FileMode.Create, FileAccess.Write);
                StreamWriter srOutput = new StreamWriter(fsOutput);
                for (pIndex = 0; pIndex < szArray.Count; pIndex++) {
                    //FOR DEBUG
                    // Console.WriteLine("* pIndex = {0}, line = {1}", pIndex, szArray[pIndex]);

                    srOutput.WriteLine(szArray[pIndex]);
                }
                srOutput.Close();
                fsOutput.Close();
                return;
            }
            else {   // file didn't exist, so create it, and don't back it up
                FileStream fsOutput = new FileStream(InputFileName, FileMode.Create, FileAccess.Write);
                StreamWriter srOutput = new StreamWriter(fsOutput);
                for (pIndex = 0; pIndex < szArray.Count; pIndex++) {
                    srOutput.WriteLine(szArray[pIndex]);
                }
                srOutput.Close();
                fsOutput.Close();
                return;
            }
        } // end of EditorWrite();

        // PageText - returns updated list pointer as int
        static int PageText(ArrayList szArray, string ParserInput, int nIndex)
        {
            Regex fullr = new Regex(@"^[pP](?<1>\d+),(?<2>\d+)", RegexOptions.Compiled);
            Regex shortr = new Regex(@"^[pP](?<1>\d+)", RegexOptions.Compiled);
            Match fullm;
            Match shortm;
            int listSuccess = 0;
            int pageCounter = 0;
            string pageReply = "";
            string pageReplyFirstChar = "";
            int PAGELENGTH = 47; // allow for Singularity "activity" line at top of console
            int PAGEWIDTH = 72;  // allow for line numbers in printouts - up to 99,999.
                                 // TODO: adjust line number range dynamically for large files
            int tempwidth = 0;
            string workstring = "";
            string tempstring = "";
            int remainder = 0;
            int division = 0;
            int linesinline = 0;
            int leftinstring = 0;
            int lowLine = 0;
            int hiLine = 0;


            //FOR DEBUGGING
            //Console.WriteLine("Current line number is {0}", nIndex);

            fullm = fullr.Match(ParserInput);
            shortm = shortr.Match(ParserInput);
            Group fullg1 = fullm.Groups[1];
            Group fullg2 = fullm.Groups[2];
            Group shortg1 = shortm.Groups[1];

            if (fullm.Success) { // we think we have two line numbers, set lowLine and hiLine accordingly

                //FOR DEBUG
                //Console.WriteLine("First line number {0}, last line number {1}", fullm.Groups[1], fullm.Groups[2]);

                Capture fullc1 = fullg1.Captures[0];
                Capture fullc2 = fullg2.Captures[0];

                // int lowLine = Convert.ToInt32(fullc1.Value);
                lowLine = Int32.Parse(fullc1.Value) - 1; // offset by one to allow for difference in starting point...

                // int hiLine = Convert.ToInt32(fullc2.Value);
                hiLine = Int32.Parse(fullc2.Value);     // but leave this one alone, due to the loop

                // test for numbers out of range or out of order
                if ((lowLine <= hiLine) && (lowLine >= 0 && lowLine <= szArray.Count) && (hiLine >= 0 && hiLine <= szArray.Count)) {
                // continue on to listing...
                }
                else { // bad arguments
                    Console.WriteLine("* Malformed arguments to page, or line out of range.");
                    Console.WriteLine("*   pnum1,num2 where num1 <= num2 and num2 <= length of file.");
                    Console.WriteLine("*   File length is {0}.", szArray.Count);
                    listSuccess = -1;
                    return listSuccess;
                }
            }
            else if (shortm.Success) { // we have one line number
                //FOR DEBUG
                //Console.WriteLine("Line number {0}", shortm.Groups[1]);

                // write out line
                Capture shortc1 = shortg1.Captures[0];

                // nIndex = Convert.ToInt32(shortc1.Value);
                nIndex = Int32.Parse(shortc1.Value);

                if (nIndex >= 1 && nIndex <= szArray.Count) { // check for line numbers in range of file
                    lowLine = nIndex - 1;
                    hiLine = nIndex;
                    // proceed to listing
                }
                else {
                    Console.WriteLine("* Line number {0} out of range. File length is {1}", nIndex, szArray.Count);
                    listSuccess = -1;
                    return listSuccess;
                }
            }
            else if ((ParserInput == "p") || (ParserInput == "P")) {  // set lowLine = 0, hiLine = szArray.Count
                lowLine = 0;
                hiLine = szArray.Count;
            }
            else {
                Console.WriteLine("Invalid match");
                listSuccess = -1;
                return listSuccess;
            }

            // print out buffer contents between lowLine and hiLine by pages
            for (nIndex = lowLine; nIndex < hiLine; nIndex++) {
                workstring = szArray[nIndex].ToString();
                tempwidth = workstring.Length;
                if (tempwidth > PAGEWIDTH) {
                    //FOR DEBUG
                    //Console.WriteLine(" need to break up line length");
                    while (division != 1) {
                        linesinline++;
                        division = tempwidth / PAGEWIDTH;
                        remainder = tempwidth % PAGEWIDTH;
                        tempwidth = tempwidth - PAGEWIDTH;
                        //FOR DEBUG
                        //Console.WriteLine("remainder = {0}, division = {1}, tempwidth = {2}, linesinline = {3}", remainder, division, tempwidth, linesinline);
                        //Console.ReadLine();
                    }
                    if (remainder != 0) {
                        linesinline++;
                        //FOR DEBUG
                        //Console.WriteLine("remainder = {0}, division = {1}, tempwidth = {2}, linesinline = {3}", remainder, division, tempwidth, linesinline);
                        //Console.ReadLine();
                    }
                    if (linesinline < (PAGELENGTH - pageCounter)) {
                        // room to print the whole wrapped line
                        leftinstring = workstring.Length;
                        while (linesinline > 0) {
                            if (leftinstring >= PAGEWIDTH) {
                                tempstring = workstring.Substring(workstring.Length - leftinstring, PAGEWIDTH);
                            }
                            else {
                                tempstring = workstring.Substring(workstring.Length - leftinstring, remainder);
                            }

                            Console.WriteLine("{0,5}: {1}", (nIndex + 1), tempstring);
                            pageCounter++;
                            linesinline--;
                            if (leftinstring > PAGEWIDTH) {
                                leftinstring = leftinstring - PAGEWIDTH;
                            }
                        }
                    }
                    else if (pageCounter <= PAGELENGTH) {
                        // less than PAGELENGTH, but not enough room to print the whole wrapped line
                        leftinstring = workstring.Length;
                        while (linesinline > 0) {
                            if (leftinstring >= PAGEWIDTH) {
                                tempstring = workstring.Substring(workstring.Length - leftinstring, PAGEWIDTH);
                            }
                            else {
                                tempstring = workstring.Substring(workstring.Length - leftinstring, remainder);
                            }

                            Console.WriteLine("{0,5}: {1}", (nIndex + 1), tempstring);
                            pageCounter++;
                            linesinline--;
                            if (leftinstring > PAGEWIDTH) {
                                leftinstring = leftinstring - PAGEWIDTH;
                            }
                            if (pageCounter > PAGELENGTH) {
                                pageCounter = 0;
                                Console.Write("-- <ENTER> -- ");
                                pageReply = GetConsoleInput();
                                if (pageReply != "") {
                                    //pageReplyFirstChar = Convert.ToString(pageReply[0]);
                                    pageReplyFirstChar = pageReply[0].ToString();
                                    switch (pageReplyFirstChar) {
                                        case "q":
                                        case "Q":
                                            return nIndex + 1;
                                        default:
                                            if (leftinstring >= PAGEWIDTH) {
                                                tempstring = workstring.Substring(workstring.Length - leftinstring, PAGEWIDTH);
                                            }
                                            else {
                                                tempstring = workstring.Substring(workstring.Length - leftinstring, remainder);
                                            }
                                            Console.WriteLine("{0,5}: {1}", (nIndex + 1), tempstring);
                                            pageCounter++;
                                            linesinline--;
                                            break;
                                    }
                                }
                            }
                        }
                    }
                    // rezero worker constants
                    remainder = 0;
                    division = 0;
                    linesinline = 0;
                    leftinstring = 0;
                    listSuccess = 1;
                }
                else {
                    Console.WriteLine("{0,5}: {1}", (nIndex + 1), szArray[nIndex]);

                    if (pageCounter < PAGELENGTH) {
                        pageCounter++;
                    }
                    else {
                        pageCounter = 0;
                        Console.Write("-- <ENTER> -- ");
                        pageReply = GetConsoleInput();
                        if (pageReply != "") {
                            //pageReplyFirstChar = Convert.ToString(pageReply[0]);
                            pageReplyFirstChar = pageReply[0].ToString();
                            switch (pageReplyFirstChar) {
                                case "q":
                                case "Q":
                                    return nIndex + 1;
                                default:
                                    break;
                            }
                        }
                    }
                listSuccess = 1;
                }
            }

            if (listSuccess == 1) {
               return nIndex; // paging worked
            }
            else {            // note that you should never get here  
               return -1;     // bad arguments, don't move line pointer
            }
        } // end of PageText

        // TransferText() - returns updated ArrayList with content merged in from external file, or the original ArrayList
        static ArrayList TransferText(ArrayList szArray, string ParserInput)
        {
            Queue transferQueue = new Queue();
            Regex transferr = new Regex(@"^[tT](?<1>\d+),(?<2>.+)", RegexOptions.Compiled);
            Match transferm;

            //FOR DEBUGGING
            //Console.WriteLine("Current line number is {0}", nIndex);

            transferm = transferr.Match(ParserInput);
            Group transferg1 = transferm.Groups[1];
            Group transferg2 = transferm.Groups[2];

            if (transferm.Success) { // we think we have a line number and a filename of some sort
                //FOR DEBUG
                // Console.WriteLine("First line number {0}, filename {1}", transferm.Groups[1], transferm.Groups[2]);

                //Put file contents to be copied into transferQueue
                Capture transferc1 = transferg1.Captures[0]; // insertion point

                // int lowLine = Convert.ToInt32(transferc1.Value);
                int lowLine = Int32.Parse(transferc1.Value);

                Capture transferc2 = transferg2.Captures[0]; // filename
                // string TransferFileName = Convert.ToString(transferc2.Value);
                string TransferFileName = transferc2.Value.ToString();

                if (File.Exists(TransferFileName)) { // file exists, so read it into a buffer
                    string TransferLine;
                    ArrayList transferContents = new ArrayList();
                    FileStream fsInput = new FileStream(TransferFileName, FileMode.Open, FileAccess.Read);
                    StreamReader srInput = new StreamReader(fsInput);
                    while ((TransferLine = srInput.ReadLine()) != null) {
                        transferContents.Add(TransferLine);
                    }
                    srInput.Close();
                    fsInput.Close();
                    for (int transferIndex = 0; transferIndex < transferContents.Count; transferIndex++) {
                        //FOR DEBUG
                        // Console.WriteLine("{0}: {1}", transferIndex, transferContents[transferIndex]);

                        transferQueue.Enqueue(transferContents[transferIndex]);
                    }
                }
                else { // file to be merged wasn't there
                    Console.WriteLine("* File to be merged doesn't exist.");
                    return szArray;
                }

                // test for numbers out of range or out of order
                if (lowLine >= 1 && lowLine <= szArray.Count) { //
                    szArray.InsertRange(lowLine - 1, transferQueue);
                    return szArray;
                }
                else if (lowLine > szArray.Count) { // check if number is past the end of the file and they want to append
                    Console.Write("* Transfer past end of file - do you want file appended? (Y/N) ");

                    string appendReply = GetConsoleInput();
                    // string appendReplyFirstChar = Convert.ToString(appendReply[0]);
                    if (appendReply != "") {
                        string appendReplyFirstChar = appendReply[0].ToString();
                        switch (appendReplyFirstChar) {
                            case "y":
                            case "Y":
                                szArray.AddRange(transferQueue);
                                break;
                            default:
                                Console.WriteLine("* Aborting transfer.");
                                break;
                        }
                    }
                    else {
                        Console.WriteLine("* Aborting transfer.");
                    }
                    return szArray;
                }
                else { // something else is wrong with the insertion point
                    Console.WriteLine("* Invalid transfer destination.");
                    Console.WriteLine("*   tnum1, filename where num1 is insertion point and filename");
                    Console.WriteLine("*   is what is to be inserted. File length is {0}.", szArray.Count);
                    return szArray;
                }
            }
            else {// bad arguments
                Console.WriteLine("* Malformed arguments to transfer.");
                Console.WriteLine("*   tnum1, filename where num1 is insertion point and filename");
                Console.WriteLine("*   is what is to be inserted. File length is {0}.", szArray.Count);
                return szArray;
            }
        } // end of TransferText

        static string GetConsoleInput() { // filter Console.ReadLine input for backspaces
            string InputString = "";
            string InputCheck = "";

            InputString = Console.ReadLine();
            if (InputString != "") {
                //FOR DEBUG
                //Console.WriteLine("* Input was {0}", InputString);
                //Console.Write("* ");
                //
                //for (int i = 0; i < InputString.Length; i++) {
                //    Console.Write("{0:x}",(int)InputString[i]);
                //}
                //Console.Write("* ");
                // END DEBUG

                // Check for backspace chars and remove them if present, but also delete the character(s) they meant to delete
                int j = 0;
                string TempString = "";
                for (int i = 0; i < InputString.Length; i++) {
                    if ((int)InputString[i] != 0x08) {
                        TempString = string.Concat(InputCheck,InputString[i].ToString());
                        InputCheck = TempString;
                        j++;
                    }
                    else {
                        InputCheck = InputCheck.Remove(j - 1,1);
                        j--;
                    }
                }
                //FOR DEBUG
                //Console.WriteLine("* Check was {0}", InputCheck);
                //Console.Write("* ");
                //
                //for (int i = 0; i < InputCheck.Length; i++) {
                //    Console.Write("{0:x}",(int)InputCheck[i]);
                //}
                //END DEBUG

            }
            return InputCheck;
        } // end of GetConsoleInput()


    }
}

