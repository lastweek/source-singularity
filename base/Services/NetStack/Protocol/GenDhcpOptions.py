#!/usr/local/bin/python
"""A program to generate C# code for DHCP option parsing.

Usage: GenDhcpOptions.py <SourceFile> <DhcpOptionsTxt>

"""

import sys
import re

# DhcpOptions.txt to C-Sharp types mappings
csTypes = {
      "Byte"           : ("byte", "value"),
      "MultiByte"      : ("byte []", "values"),
      "Word"           : ("ushort", "value"),
      "MultiWord"      : ("ushort []", "values"),
      "DWord"          : ("uint", "value"),
      "MultiDWord"     : ("uint []", "values"),
      "IPv4"           : ("IPv4", "address"),
      "MultiIPv4"      : ("IPv4 []", "addresses"),
      "String"         : ("char []", "chars")
}

def GetDhcpOptionValues(lines):
   optionPattern = re.compile("^([0-9]+)\s+(\w+)\s+(\w+)")
   options = []
   for line in lines:
      match = optionPattern.match(line)
      if match != None:
         options.append(match.groups())
   return options

def WriteDhcpFragment(optionValue, optionName, typeName):

   (csArgType, csArgName) = csTypes[typeName]

   print """
    public class Dhcp%s
    {
        public const byte OptionCode = %s;

        public static IDhcpOption Create(%s %s)
        {
            return new Dhcp%sOption(OptionCode, %s);
        }
     }""" % (optionName, optionValue, csArgType,
                csArgName, typeName, csArgName)

def OutputGeneratedCode(options):
   for o in options:
      WriteDhcpFragment(o[0], o[1], o[2])

def OutputGeneratedTable(options):
   for o in options:
      print "            parsers.Add(Dhcp%s.OptionCode," % o[1]
      print "                        new Parser(\"%s\"," % o[1]
      print "                                   new ParseDhcpOption(Dhcp%sOption.Parse)));" % o[2]

def OutputSourceAndGeneratedCode(sourceLines, options):
   begin_table_region = re.compile("^#region\s+GeneratedTable.*")
   end_table_region = re.compile("^#endregion\s+//\s+GeneratedTable.*")
   in_table_region = False

   sourceIter = iter(sourceLines)
   while True:
      try: line = sourceIter.next()
      except StopIteration: break

      if in_table_region == False:
         print line,
      if begin_table_region.match(line):
         in_table_region = True
         OutputGeneratedTable(options)
      if end_table_region.match(line):
         print line,
         break;

   begin_class_region = re.compile("^#region\s+GeneratedClasses.*")
   end_class_region = re.compile("^#endregion\s+//\s+GeneratedClasses.*")
   in_class_region = False

   while True:
      try: line = sourceIter.next()
      except StopIteration: break
      if in_class_region == False:
         print line,
      if begin_class_region.match(line):
         in_class_region = True
         OutputGeneratedCode(options)
      if end_class_region.match(line):
         in_class_region = False
         print line,

def main():
   if len(sys.argv) != 3:
      print "Usage: GenDhcpOptions <csfile> <optionstxtfile>"
      return 2

   sourceFile  = open(sys.argv[1], 'r')
   optionsFile = open(sys.argv[2], 'r')

   sourceLines = sourceFile.readlines()
   optionLines = optionsFile.readlines()

   dhcpOptions = GetDhcpOptionValues(optionLines)
   OutputSourceAndGeneratedCode(sourceLines, dhcpOptions)
   return 0

if __name__ == "__main__":
   sys.exit(main())
