////////////////////////////////////////////////////////////////////////////////
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
//  Microsoft Research Singularity
//

// This tool is used to take .csunion files and generate .cs files. The format of
// the .csunion file is as follows:
//
// <header section>
// %%
// <in class section>
// %%
// datatype <name> : OptionalBaseClass {
//     <type> <name>(<arguments>), // Comments can be specified with //
//     <type> <name>(<arguments>), // If no arguments, parens can be omitted
//     ...
//     %%
//     [Optional section of raw program text to emit directly into the class]
//     %%
// }
//
// <more datatypes>
// ...
// 
// The header section is simply emitted at the top of the generated file beneath
// the comment block. The datatype expressions each describe a disjoint union with
// a list of alternatives, each of which can specify associated data arguments.
//
// The output .cs file will contain the following:
//
// * A class for each datatype.
// * A simple subclass for each alternative with more than one argument.
// * An enum TagValue with a value for each alternative and a Tag property.
// * Static constructor methods for each alternative (currently disjoint unions
//   are immutable, although set methods could be emitted).
// * "GetAs" methods for each alternative that check the tag with Debug.Assert().
// * A commented-out method ExampleUsage() demonstrating how to switch
//   on the tag and extract the corresponding value. This should be
//   used as a template for code that reads a value of the union type.
//
// See the example file Tree.csunion under the test subdirectory, and the example
// project MkUnionTest.csproj for an example of how to build a .csunion file
// using <CsUnionFile>.

using System;
using System.IO;
using System.Text.RegularExpressions;
using System.Collections.Generic;

namespace Microsoft.Singularity.Applications
{
    public class MkUnion
    {
        private class UnionDefinition
        {
            public string Name;
            public List<UnionAlternative> Alternatives;
            public string BaseClass;
            public string RawText;
        }

        private class UnionAlternative
        {
            public string Name;
            public List<UnionAlternativeMember> Contents;
        }

        private class UnionAlternativeMember
        {
            public string Type;
            public string Name;
        }

        private static List<UnionDefinition> Parse(TextReader inputReader)
        {
            List<UnionDefinition> result = new List<UnionDefinition>();
            string allText = inputReader.ReadToEnd();

            // Remove comments and newlines
            allText = new Regex(@"/\*.*?\*/", RegexOptions.Multiline).Replace(allText, "");
            allText = new Regex(@"//.*$", RegexOptions.Multiline).Replace(allText, "");
            allText = new Regex(@"[\r\n]+").Replace(allText, "");

            string identifier = @"[A-Za-z][A-Za-z0-9]*";
            foreach (Match matchDef in new Regex(@"datatype\s+(" + identifier + @")\s*(:\s*([^ ]+)\s*)?{([^}%]*)(%%(.*?)%%)?}").Matches(allText)) {
                UnionDefinition definition = new UnionDefinition();
                definition.Name = matchDef.Groups[1].Value;
                definition.Alternatives = new List<UnionAlternative>();

                definition.BaseClass = matchDef.Groups[3].Success ? matchDef.Groups[3].Value : "";
                definition.RawText = matchDef.Groups[5].Success ? matchDef.Groups[6].Value : "";
                
                string alternatives = matchDef.Groups[4].Value;
                foreach (Match matchAlt in new Regex(@"\b(" + identifier + @")\s*(\((.*?)\))?").Matches(alternatives)) {
                    UnionAlternative alternative = new UnionAlternative();
                    alternative.Name = matchAlt.Groups[1].Value;
                    alternative.Contents = new List<UnionAlternativeMember>();

                    string[] contents = matchAlt.Groups[3].Value.Split(new char[] { ' ', ',' },
                                                                       StringSplitOptions.RemoveEmptyEntries);
                    if ((contents.Length % 2) != 0) {
                        throw new Exception("Must specify type and name for each alternative data field. Types cannot contain spaces.");
                    }
                    for (int i = 0; i < contents.Length; i += 2) {
                        UnionAlternativeMember member = new UnionAlternativeMember();
                        member.Type = contents[i];
                        member.Name = contents[i + 1];
                        alternative.Contents.Add(member);
                    }

                    definition.Alternatives.Add(alternative);
                }

                result.Add(definition);
            }
            
            return result;
        }

        private static string Capitalize(string s) {
            if (s.Length == 0) {
                return s;
            } else {
                return new string(Char.ToUpper(s[0]), 1) + s.Substring(1);
            }
        }

        private static string Uncapitalize(string s) {
            if (s.Length == 0) {
                return s;
            } else {
                return new string(Char.ToLower(s[0]), 1) + s.Substring(1);
            }
        }

        private static void OutputUnionClass(TextWriter outputWriter, UnionDefinition definition, int indent)
        {
            outputWriter.Write(new string(' ', indent*1) + "public class " + definition.Name);
            if (definition.BaseClass != "") {
                outputWriter.Write(" : " + definition.BaseClass);
            }
            outputWriter.WriteLine();
            outputWriter.WriteLine(new string(' ', indent*1) + "{");

            //
            // Tag stuff
            //
            outputWriter.WriteLine(new string(' ', indent*2) + "public enum TagValue");
            outputWriter.WriteLine(new string(' ', indent*2) + "{");
            foreach (UnionAlternative alternative in definition.Alternatives) {
                outputWriter.WriteLine(new string(' ', indent*3) + alternative.Name + ",");
            }
            outputWriter.WriteLine(new string(' ', indent*2) + "}\r\n");

            outputWriter.WriteLine(new string(' ', indent*2) + "private TagValue tag;\r\n");

            outputWriter.WriteLine(new string(' ', indent*2) + "public TagValue Tag");
            outputWriter.WriteLine(new string(' ', indent*2) + "{");
            outputWriter.WriteLine(new string(' ', indent*3) + "get {");
            outputWriter.WriteLine(new string(' ', indent*4) + "return tag;");
            outputWriter.WriteLine(new string(' ', indent*3) + "}");
            outputWriter.WriteLine(new string(' ', indent*2) + "}");
            outputWriter.WriteLine("");

            //
            // Generate subclasses for alternatives with contents
            //
            foreach (UnionAlternative alternative in definition.Alternatives)
            {
                if (alternative.Contents.Count > 1) {
                    outputWriter.WriteLine(new string(' ', indent*2) + "public class " + alternative.Name);
                    outputWriter.WriteLine(new string(' ', indent*2) + "{");
                    foreach (UnionAlternativeMember member in alternative.Contents)
                    {
                        outputWriter.WriteLine(new string(' ', indent*3) + "public " + member.Type + " " + Capitalize(member.Name) + ";");
                    }
                    outputWriter.WriteLine("");
                    outputWriter.Write(new string(' ', indent*3) + "public " + alternative.Name + "(");
                    outputWriter.Write(String.Join(", ",
                        alternative.Contents.ConvertAll<string>(delegate(UnionAlternativeMember member) {
                            return member.Type + " " + member.Name;
                        }).ToArray()));
                    outputWriter.WriteLine(") {");
                    foreach (UnionAlternativeMember member in alternative.Contents)
                    {
                        outputWriter.WriteLine(new string(' ', indent*4) + "this." + Capitalize(member.Name) + " = " + member.Name + ";");
                    }
                    outputWriter.WriteLine(new string(' ', indent*3) + "}");

                    outputWriter.WriteLine(new string(' ', indent*2) + "}\r\n");
                }
            }

            //
            // Value field and private constructor
            //
            outputWriter.WriteLine(new string(' ', indent*2) + "private object value;\r\n");
                
            outputWriter.WriteLine(new string(' ', indent*2) + "private " + definition.Name + "(TagValue tag, object value) {");
            outputWriter.WriteLine(new string(' ', indent*3) + "this.tag = tag;");
            outputWriter.WriteLine(new string(' ', indent*3) + "this.value = value;");
            outputWriter.WriteLine(new string(' ', indent*2) + "}\r\n");

            //
            // Generate static constructors
            //
            foreach (UnionAlternative alternative in definition.Alternatives) {
                outputWriter.Write(new string(' ', indent*2) + "public static " + definition.Name + " Create" + Capitalize(alternative.Name) + "(");
                outputWriter.Write(String.Join(", ",
                    alternative.Contents.ConvertAll<string>(delegate(UnionAlternativeMember member) {
                        return member.Type + " " + member.Name;
                    }).ToArray()));
                outputWriter.WriteLine(")");
                outputWriter.WriteLine(new string(' ', indent*2) + "{");
                outputWriter.Write(new string(' ', indent*3) + "return new " + definition.Name + "(TagValue." + alternative.Name + ", ");
                if (alternative.Contents.Count == 0) {
                    outputWriter.Write("null");
                }
                else if (alternative.Contents.Count == 1) {
                    outputWriter.Write(alternative.Contents[0].Name);
                }
                else {
                    outputWriter.Write("new " + alternative.Name + "(");
                    outputWriter.Write(String.Join(", ",
                        alternative.Contents.ConvertAll<string>(delegate(UnionAlternativeMember member)
                    {
                        return member.Name;
                    }).ToArray()));
                    outputWriter.Write(")");
                }
                outputWriter.WriteLine(");");
                outputWriter.WriteLine(new string(' ', indent*2) + "}\r\n");
            }

            //
            // Read-only accessors
            //

            foreach (UnionAlternative alternative in definition.Alternatives) {
                if (alternative.Contents.Count > 0) {
                    string returnType;
                    if (alternative.Contents.Count == 1) {
                        returnType = alternative.Contents[0].Type;
                    }
                    else {
                        returnType = alternative.Name;
                    }
                    outputWriter.WriteLine(new string(' ', indent * 2) + "public " + returnType + " GetAs" + Capitalize(alternative.Name) + "()");
                    outputWriter.WriteLine(new string(' ', indent * 2) + "{");
                    outputWriter.WriteLine(new string(' ', indent * 3) + "Debug.Assert(Tag == TagValue." + alternative.Name + ", \"Type error: tried to access disjoint union as '" + alternative.Name + "' but tag does not match\");");
                    outputWriter.WriteLine(new string(' ', indent * 3) + "return (" + returnType + ")value;");
                    outputWriter.WriteLine(new string(' ', indent * 2) + "}\r\n");
                }
            }

            //
            // Example usage template
            //

            outputWriter.WriteLine("#if false");
            outputWriter.WriteLine(new string(' ', indent*2) + "// Example usage template for this disjoint union type");
            outputWriter.WriteLine(new string(' ', indent*2) + "public static void ExampleUsage(" + definition.Name + " " + Uncapitalize(definition.Name) + ")");
            outputWriter.WriteLine(new string(' ', indent*2) + "{");
            outputWriter.WriteLine(new string(' ', indent*3) + "switch (" + Uncapitalize(definition.Name) + ".Tag) {");
            foreach (UnionAlternative alternative in definition.Alternatives) {
                outputWriter.WriteLine(new string(' ', indent*4) + "case " + definition.Name + ".TagValue." + alternative.Name + ":");
                if (alternative.Contents.Count > 0) {
                    string returnType;
                    if (alternative.Contents.Count == 1) {
                        returnType = alternative.Contents[0].Type;
                    }
                    else {
                        returnType = definition.Name + "." + alternative.Name;
                    }
                    outputWriter.WriteLine(new string(' ', indent*5) + returnType + " " +
                                           Uncapitalize(alternative.Name) + " = " + Uncapitalize(definition.Name) + ".GetAs" +
                                           Capitalize(alternative.Name) + "();");
                }
                outputWriter.WriteLine(new string(' ', indent*5) + "break;");
            }
            outputWriter.WriteLine(new string(' ', indent*4) + "default:");
            outputWriter.WriteLine(new string(' ', indent*5) + "Debug.Assert(false, \"Unhandled alternative in switch over '" + definition.Name + "'\");");
            outputWriter.WriteLine(new string(' ', indent*5) + "break;");

            outputWriter.WriteLine(new string(' ', indent*3) + "}");
            outputWriter.WriteLine(new string(' ', indent*2) + "}");
            outputWriter.WriteLine("#endif");

            outputWriter.WriteLine(definition.RawText);

            outputWriter.WriteLine(new string(' ', indent*1) + "}\r\n");
        }

        private static void Usage()
        {
            Console.WriteLine("Usage: mkunion <input filename> <namespace> <output filename>");
        }

        public static void Main(string[] args)
        {
            if (args.Length < 3) {
                Usage();
                return;
            }
            
            string inputFilename = args[0];
            string outputNamespace = args[1];
            string outputFilename = args[2];

            try {
                using (TextReader inputReader = File.OpenText(inputFilename)) {
                    using (TextWriter outputWriter = new StreamWriter(outputFilename)) {
                        outputWriter.WriteLine(
                            "///////////////////////////////////////////////////////////////////////////////\r\n" +
                            "//\r\n" +
                            "//  Copyright (c) Microsoft Corporation.  All rights reserved.\r\n" +
                            "//\r\n" +
                            "//  Microsoft Research Singularity\r\n" +
                            "//\r\n" +
                            "//  This file is automatically generated by mkunion. Do not check it in or edit it.\r\n" + 
                            "//\r\n\r\n");

                        outputWriter.WriteLine("using System.Diagnostics;\r\n\r\n");

                        while (true) {
                            string line = inputReader.ReadLine();
                            if (line == null || line == "%%") {
                                break;
                            }
                            else {
                                outputWriter.WriteLine(line);
                            }
                        }

                        outputWriter.WriteLine("namespace " + outputNamespace + "\r\n{\r\n");

                        List<UnionDefinition> definitions = Parse(inputReader);
                        foreach (UnionDefinition definition in definitions) {
                            OutputUnionClass(outputWriter, definition, /*indent*/4);
                        }

                        outputWriter.WriteLine("}\r\n");
                    }
                }
            }
            catch (Exception e) {
                Console.WriteLine("mkunion failed: " + e.Message + "\r\n" + e.StackTrace);
                Environment.ExitCode = 1;
            }
            Environment.ExitCode = 0;
        }
    }
}