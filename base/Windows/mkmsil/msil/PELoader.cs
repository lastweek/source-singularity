//
// Copyright (c) Microsoft Corporation.   All rights reserved.
//

using System;
using System.IO;
using System.Runtime.InteropServices;

namespace Bartok.MSIL
{

  public class PELoader {

      // Constructor Methods

      public PELoader(Stream stream)
          : this(stream, "<anonymous>")
      {
      }

      public PELoader(Stream stream, String path)
      {
          this.path = path;
          this.stream = stream;
          this.loadPEHeaders();
      }

      // Access Methods

      internal Stream getStream() {
          return this.stream;
      }

      internal int getEntryPoint() {
          return this.comHeader.entryPointToken;
      }

      internal int getMetaDataOffset() {
          return this.VaToOffset(this.comHeader.metaData.virtualAddress);
      }

      internal int getResourceOffset() {
          return this.VaToOffsetSafe(this.comHeader.resources.virtualAddress);
      }

      internal int getRelocationOffset() {
          int limit = ntHeader.numberOfSections;
          for (int i = 0; i < limit; i++) {
              SectionHeader section = this.sectionArray[i];
              if (section.name.StartsWith(".reloc")) {
                  return this.VaToOffset(section.virtualAddress);
              }
          }
          return 0;
      }

      internal int getVtableFixupOffset() {
          return this.VaToOffsetSafe(this.comHeader.vtableFixups.virtualAddress);
      }

      internal int getDelayIATOffset() {
          return this.VaToOffsetSafe(this.ntHeader.dataDirectory[13].virtualAddress);
      }

      internal int getImageBase() {
          return ntHeader.imageBase;
      }

      internal int getResourceSize() {
          return this.comHeader.resources.size;
      }

      internal int getVtableFixupSize() {
          return this.comHeader.vtableFixups.size;
      }

      internal int getDelayIATSize() {
          return this.ntHeader.dataDirectory[13].size;
      }

      internal bool IsExecutableImage() {
          return ((this.ntHeader.characteristics & NTHeader.IMAGE_FILE_EXECUTABLE_IMAGE) != 0) &&
              ((this.ntHeader.characteristics & NTHeader.IMAGE_FILE_DLL) == 0);
      }

      // Output Routines

      internal void DumpHeader(StreamWriter outputStream) {
          outputStream.WriteLine("// PE Header:");
          outputStream.WriteLine();
          this.ntHeader.DumpLimitedToStream(outputStream, "// ");

          this.DumpIAT(outputStream, "Import directory", ref ntHeader.dataDirectory[1]);
          // this.DumpIAT(outputStream, "Import Address Table", ref ntHeader.dataDirectory[12]);
          // this.DumpIAT(outputStream, "Delay Load Import Address Table", ref ntHeader.dataDirectory[13]);

          outputStream.WriteLine("// CLR Header:");
          outputStream.WriteLine("// "+this.comHeader.cb.ToString("x8")+" Header size");
          outputStream.WriteLine("// "+this.comHeader.majorRuntimeVersion.ToString("x8")+" Major runtime version");
          outputStream.WriteLine("// "+this.comHeader.minorRuntimeVersion.ToString("x8")+" Minor runtime version");
          outputStream.WriteLine("// "+this.comHeader.flags.ToString("x8")+" Flags");
          outputStream.WriteLine("// "+this.comHeader.entryPointToken.ToString("x8")+" Entrypoint token");
          outputStream.WriteLine("// "+this.comHeader.metaData.virtualAddress.ToString("x8")+" ["+this.comHeader.metaData.size.ToString("x8")+"] address [size] of Metadata directory");
          outputStream.WriteLine("// "+this.comHeader.resources.virtualAddress.ToString("x8")+" ["+this.comHeader.resources.size.ToString("x8")+"] address [size] of Resources directory");
          outputStream.WriteLine("// "+this.comHeader.strongNameSignature.virtualAddress.ToString("x8")+" ["+this.comHeader.strongNameSignature.size.ToString("x8")+"] address [size] of Strong name signature");
          outputStream.WriteLine("// "+this.comHeader.codeManagerTable.virtualAddress.ToString("x8")+" ["+this.comHeader.codeManagerTable.size.ToString("x8")+"] address [size] of CodeManager table");
          outputStream.WriteLine("// "+this.comHeader.vtableFixups.virtualAddress.ToString("x8")+" ["+this.comHeader.vtableFixups.size.ToString("x8")+"] address [size] of VTableFixups directory");
          outputStream.WriteLine("// "+this.comHeader.exportAddressTableJumps.virtualAddress.ToString("x8")+" ["+this.comHeader.exportAddressTableJumps.size.ToString("x8")+"] address [size] of Export address table");
          outputStream.WriteLine("// "+this.comHeader.managedNativeHeader.virtualAddress.ToString("x8")+" ["+this.comHeader.managedNativeHeader.size.ToString("x8")+"] address [size] of Precompile header");
      }

      internal void DumpCodeManager(StreamWriter outputStream) {
          outputStream.WriteLine("// Code Manager Table");
          if (this.comHeader.codeManagerTable.size == 0) {
              outputStream.WriteLine("//  default");
              return;
          }
          // BUGBUG
          throw new NotYetImplemented("DumpCodeManager");
      }

      internal void DumpVTables(StreamWriter outputStream) {
          outputStream.WriteLine("// VTableFixup Directory:");
          if (comHeader.vtableFixups.virtualAddress == 0) {
              outputStream.WriteLine("//  No data.");
              return;
          }
          // BUGBUG
          throw new NotYetImplemented("DumpVTables");
      }

      internal void DumpEATTable(StreamWriter outputStream) {
          outputStream.WriteLine("// Export Address Table Jumps:");
          if (comHeader.exportAddressTableJumps.virtualAddress == 0) {
              outputStream.WriteLine("//  No data.");
              return;
          }
          // BUGBUG
          throw new NotYetImplemented("DumpEATTable");
      }

      internal void DumpStatistics(StreamWriter outputStream) {
          throw new NotYetImplemented("DumpStatistics");
      }

      public override String ToString() {
          return "PELoader("+path+")";
      }

      // Private Helper Methods

      private void loadPEHeaders() {
          // Ensure that we are at the beginning of the stream.
          this.stream.Seek(0L, SeekOrigin.Begin);
          DOSHeader dosHeader = new DOSHeader(this.stream);
          // Move on to the NT header
          this.stream.Seek(dosHeader.lfanew, SeekOrigin.Begin);
          BinaryReader reader = new BinaryReader(this.stream);
          this.ntHeader = new NTHeader(reader);
          // Load the sections
          int sectionCount = ntHeader.numberOfSections;
          SectionHeader[] sectionArray = new SectionHeader[sectionCount];
          this.sectionArray = sectionArray;
          for (int i = 0; i < sectionCount; i++) {
              this.sectionArray[i] = new SectionHeader(reader);
              int startAddr = sectionArray[i].virtualAddress;
              int endAddr = sectionArray[i].virtualAddress+sectionArray[i].sizeOfRawData;
              int delta = sectionArray[i].pointerToRawData-sectionArray[i].virtualAddress;
          }
          // Load the COM/COR20 header
          DirectoryEntry entry =
              this.ntHeader.dataDirectory[COMHeader.ENTRYINDEX];
          int comOffset = this.VaToOffset(entry.virtualAddress);
          this.stream.Seek(comOffset, SeekOrigin.Begin);
          this.comHeader = new COMHeader(this.stream);
      }

      internal int VaToOffset(int virtualAddress) {
          int limit = ntHeader.numberOfSections;
          for (int i = 0; i < limit; i++) {
              SectionHeader section = this.sectionArray[i];
              if (virtualAddress >= section.virtualAddress &&
                  virtualAddress < (section.virtualAddress + section.sizeOfRawData)) {
                  return (virtualAddress -
                          section.virtualAddress +
                          section.pointerToRawData);
              }
          }
          throw new IllegalPEFormatException("Unknown VA "+virtualAddress);
      }

      internal int VaToOffsetSafe(int virtualAddress) {
          int limit = ntHeader.numberOfSections;
          for (int i = 0; i < limit; i++) {
              SectionHeader section = this.sectionArray[i];
              if (virtualAddress >= section.virtualAddress &&
                  virtualAddress < (section.virtualAddress + section.sizeOfRawData)) {
                  return (virtualAddress -
                          section.virtualAddress +
                          section.pointerToRawData);
              }
          }
          return -1;
      }

      private void DumpIAT(StreamWriter outputStream,
                           String title,
                           ref DirectoryEntry entry) {
          outputStream.WriteLine("// "+title);
          if (entry.size == 0) {
              outputStream.WriteLine("// No data.");
              outputStream.WriteLine();
              return;
          }
          if (entry.size < ImportDescriptor.SIZE) {
              outputStream.WriteLine("Not enough data for IMAGE_IMPORT_DESCRIPTOR");
              return;
          }
          int importOffset = this.VaToOffset(entry.virtualAddress);
          while (true) {
              this.stream.Seek(importOffset, SeekOrigin.Begin);
              ImportDescriptor importDescriptor =
                  new ImportDescriptor(this.stream);
              if (importDescriptor.firstChunk == 0) {
                  return;
              }
              String name = null;
              if (importDescriptor.name != 0) {
                  int nameOffset = this.VaToOffset(importDescriptor.name);
                  name = this.readString(nameOffset);
              }
              outputStream.WriteLine("//     "+name);
              importDescriptor.DumpToStream(outputStream, "//              ");
              outputStream.WriteLine("//");

              int importTableOffset =
                  this.VaToOffset(importDescriptor.firstChunk);
              while (true) {
                  this.stream.Seek(importTableOffset, SeekOrigin.Begin);
                  BinaryReader intReader = new BinaryReader(this.stream);
                  int importTableID = intReader.ReadInt32();
                  if (importTableID == 0) break;
                  outputStream.WriteLine("importTableID is "+importTableID.ToString("x"));
                  outputStream.Flush();
                  int nameStringOffset =
                      this.VaToOffset(importTableID & 0x7fffffff);
                  this.stream.Seek(nameStringOffset, SeekOrigin.Begin);
                  intReader = new BinaryReader(this.stream);
                  if ((importTableID & 0x8000000) != 0) {
                      outputStream.WriteLine("//              "+intReader.ReadInt16().ToString("x8")+" by ordinal "+(importTableID & 0x7ffffff));
                  }
                  else {
                      outputStream.WriteLine("//              "+intReader.ReadInt16().ToString("x8")+" "+this.readString(nameStringOffset+2));
                  }
                  importTableOffset += 4;
              }
              outputStream.WriteLine();
              importOffset += ImportDescriptor.SIZE;
          }
      }

      internal Section[] loadSections() {
          Section[] sections = new Section[sectionArray.Length];
          for (int i = 0; i < sectionArray.Length; i++) {
              Section section = new Section(sectionArray[i]);
              section.LoadSection(this);
              sections[i] = section;
          }
          return sections;
      }

      public String readString(int offset) {
          this.stream.Seek(offset, SeekOrigin.Begin);
          int length = 8;
          int startIndex = 0;
          byte[] buffer = new byte[length];
          while (true) {
              int count = this.stream.Read(buffer, startIndex,
                                           length - startIndex);
              if (count == 0) {
                  throw new Exception("Got 0 bytes from Read of file");
              }
              int limit = startIndex + count;
              for (int i = startIndex; i < limit; i++) {
                  if (buffer[i] == 0) {
                      char[] chars = new char[i];
                      for (int j = 0; j < i; j++) {
                          chars[j] = (char) buffer[j];
                      }
                      return new String(chars);
                  }
              }
              byte[] newBuffer = new byte[2*length];
              for (int i = 0; i < length; i++) {
                  newBuffer[i] = buffer[i];
              }
              length = 2*length;
              startIndex += count;
              buffer = newBuffer;
          }
      }

      // Private State

      private String path;
      private Stream stream;
      private NTHeader ntHeader;
      private COMHeader comHeader;
      private SectionHeader[] sectionArray;

      // Nested classes

      internal class DOSHeader {
          // Corresponds to the WinNT IMAGE_DOS_HEADER data structure

          // How to read from stream

          internal DOSHeader(Stream stream):
              this(new BinaryReader(stream))
          { }

          internal DOSHeader(BinaryReader reader) {
              // We could just read the magic and lfanew fields, but
              // let's read everything for now
              this.magic    = reader.ReadInt16();
              this.cblp     = reader.ReadInt16();
              this.cp       = reader.ReadInt16();
              this.crlc     = reader.ReadInt16();
              this.cparhdr  = reader.ReadInt16();
              this.minalloc = reader.ReadInt16();
              this.maxalloc = reader.ReadInt16();
              this.ss       = reader.ReadInt16();
              this.sp       = reader.ReadInt16();
              this.csum     = reader.ReadInt16();
              this.ip       = reader.ReadInt16();
              this.cs       = reader.ReadInt16();
              this.lfarlc   = reader.ReadInt16();
              this.ovno     = reader.ReadInt16();
              this.res_0    = reader.ReadInt16();
              this.res_1    = reader.ReadInt16();
              this.res_2    = reader.ReadInt16();
              this.res_3    = reader.ReadInt16();
              this.oemid    = reader.ReadInt16();
              this.oeminfo  = reader.ReadInt16();
              this.res2_0   = reader.ReadInt16();
              this.res2_1   = reader.ReadInt16();
              this.res2_2   = reader.ReadInt16();
              this.res2_3   = reader.ReadInt16();
              this.res2_4   = reader.ReadInt16();
              this.res2_5   = reader.ReadInt16();
              this.res2_6   = reader.ReadInt16();
              this.res2_7   = reader.ReadInt16();
              this.res2_8   = reader.ReadInt16();
              this.res2_9   = reader.ReadInt16();
              this.lfanew   = reader.ReadInt32();
              // Verify that we have a correct DOS header and a valid
              // pointer to the NT header
              if (this.magic != DOSHeader.IMAGE_DOS_SIGNATURE ||
                  this.lfanew <= 0) {
                  throw new IllegalPEFormatException("DOS header problems");
              }
          }

          // State

          internal short magic;    // Magic number
          internal short cblp;     // Bytes on last page of file
          internal short cp;       // Pages in file
          internal short crlc;     // Relocations
          internal short cparhdr;  // Size of header in paragraphs
          internal short minalloc; // Minimum extra paragraphs needed
          internal short maxalloc; // Maximum extra paragraphs needed
          internal short ss;       // Initial (relative) SS value
          internal short sp;       // Initial SP value
          internal short csum;     // Checksum
          internal short ip;       // Initial IP value
          internal short cs;       // Initial (relative) CS value
          internal short lfarlc;   // File address of relocation table
          internal short ovno;     // Overlay number
          internal short res_0;    // Reserved words
          internal short res_1;
          internal short res_2;
          internal short res_3;
          internal short oemid;    // OEM identifier (for e_oeminfo)
          internal short oeminfo;  // OEM information; e_oemid specific
          internal short res2_0;   // Reserved words
          internal short res2_1;
          internal short res2_2;
          internal short res2_3;
          internal short res2_4;
          internal short res2_5;
          internal short res2_6;
          internal short res2_7;
          internal short res2_8;
          internal short res2_9;
          internal int lfanew;   // File address of new exe header

          internal const short IMAGE_DOS_SIGNATURE = 0x5A4D;
      }

      internal class NTHeader {
          // Corresponds to the WinNT IMAGE_NT_HEADERS data structure

          // How to read from stream

          internal NTHeader(Stream stream):
              this(new BinaryReader(stream))
          { }

          internal NTHeader(BinaryReader reader) {
              // We could read a selection of these, but read every
              // field for now.
              this.signature                   = reader.ReadInt32();
              this.machine                     = reader.ReadInt16();
              this.numberOfSections            = reader.ReadInt16();
              this.timeDateStamp               = reader.ReadInt32();
              this.pointerToSymbolTable        = reader.ReadInt32();
              this.numberOfSymbols             = reader.ReadInt32();
              this.sizeOfOptionalHeader        = reader.ReadInt16();
              this.characteristics             = reader.ReadInt16();
              this.magic                       = reader.ReadInt16();
              this.majorLinkerVersion          = reader.ReadByte();
              this.minorLinkerVersion          = reader.ReadByte();
              this.sizeOfCode                  = reader.ReadInt32();
              this.sizeOfInitializedData       = reader.ReadInt32();
              this.sizeOfUninitializedData     = reader.ReadInt32();
              this.addressOfEntryPoint         = reader.ReadInt32();
              this.baseOfCode                  = reader.ReadInt32();
              this.baseOfData                  = reader.ReadInt32();
              this.imageBase                   = reader.ReadInt32();
              this.sectionAlignment            = reader.ReadInt32();
              this.fileAlignment               = reader.ReadInt32();
              this.majorOperatingSystemVersion = reader.ReadInt16();
              this.minorOperatingSystemVersion = reader.ReadInt16();
              this.majorImageVersion           = reader.ReadInt16();
              this.minorImageVersion           = reader.ReadInt16();
              this.majorSubsystemVersion       = reader.ReadInt16();
              this.minorSubsystemVersion       = reader.ReadInt16();
              this.win32VersionValue           = reader.ReadInt32();
              this.sizeOfImage                 = reader.ReadInt32();
              this.sizeOfHeaders               = reader.ReadInt32();
              this.checkSum                    = reader.ReadInt32();
              this.subsystem                   = reader.ReadInt16();
              this.dllCharacteristics          = reader.ReadInt16();
              this.sizeOfStackReserve          = reader.ReadInt32();
              this.sizeOfStackCommit           = reader.ReadInt32();
              this.sizeOfHeapReserve           = reader.ReadInt32();
              this.sizeOfHeapCommit            = reader.ReadInt32();
              this.loaderFlags                 = reader.ReadInt32();
              int count                        = reader.ReadInt32();
              this.numberOfRvaAndSizes         = count;
              DirectoryEntry[] directoryArray  = new DirectoryEntry[count];
              this.dataDirectory = directoryArray;
              for (int i = 0; i < count; i++) {
                  directoryArray[i] = new DirectoryEntry(reader);
              }
              // Verify that we have a valid NT header
              if (this.signature != NTHeader.IMAGE_NT_SIGNATURE ||
                  this.sizeOfOptionalHeader != NTHeader.IMAGE_SIZEOF_NT_OPTIONAL32_HEADER ||
                  this.magic != NTHeader.IMAGE_NT_OPTIONAL_HDR32_MAGIC ||
                  this.numberOfRvaAndSizes != 16) {
                  throw new IllegalPEFormatException("NT header problems");
              }
          }

          // Output Routines

          internal void DumpLimitedToStream(StreamWriter outputStream,
                                            String prefix) {
              outputStream.WriteLine(prefix+
                                     "Subsystem:                      "+
                                     this.subsystem.ToString("x8"));
              outputStream.WriteLine(prefix+
                                     "Native entry point address:     "+
                                     this.addressOfEntryPoint.ToString("x8"));
              outputStream.WriteLine(prefix+
                                     "Image base:                     "+
                                     this.imageBase.ToString("x8"));
              outputStream.WriteLine(prefix+
                                     "Section alignment:              "+
                                     this.sectionAlignment.ToString("x8"));
              outputStream.WriteLine(prefix+
                                     "File alignment:                 "+
                                     this.fileAlignment.ToString("x8"));
              outputStream.WriteLine(prefix+
                                     "Stack reserve size:             "+
                                     this.sizeOfStackReserve.ToString("x8"));
              outputStream.WriteLine(prefix+
                                     "Stack commit size:              "+
                                     this.sizeOfStackCommit.ToString("x8"));
              outputStream.WriteLine(prefix+
                                     "Directories:                    "+
                                     this.numberOfRvaAndSizes.ToString("x8"));
              String indentedPrefix = prefix+"    ";
              this.dataDirectory[0].DumpToStream(outputStream, indentedPrefix,
                                                 " of Export directory ");
              this.dataDirectory[1].DumpToStream(outputStream, indentedPrefix,
                                                 " of Import directory");
              this.dataDirectory[2].DumpToStream(outputStream, indentedPrefix,
                                                 " of Resource directory");
              this.dataDirectory[3].DumpToStream(outputStream, indentedPrefix,
                                                 " of Exception directory");
              this.dataDirectory[4].DumpToStream(outputStream, indentedPrefix,
                                                 " of Security directory");
              this.dataDirectory[5].DumpToStream(outputStream, indentedPrefix,
                                                 " of Base Relocation Table");
              this.dataDirectory[6].DumpToStream(outputStream, indentedPrefix,
                                                 " of Debug directory");
              this.dataDirectory[7].DumpToStream(outputStream, indentedPrefix,
                                                 " of Architecture specific");
              this.dataDirectory[8].DumpToStream(outputStream, indentedPrefix,
                                                 " of Global pointer directory");
              this.dataDirectory[9].DumpToStream(outputStream, indentedPrefix,
                                                 " of TLS directory ");
              this.dataDirectory[10].DumpToStream(outputStream, indentedPrefix,
                                                  " of Load config directory");
              this.dataDirectory[11].DumpToStream(outputStream, indentedPrefix,
                                                  " of Bound import directory");
              this.dataDirectory[12].DumpToStream(outputStream, indentedPrefix,
                                                  " of Import Address Table");
              this.dataDirectory[13].DumpToStream(outputStream, indentedPrefix,
                                                  " of Delay Load IAT");
              this.dataDirectory[14].DumpToStream(outputStream, indentedPrefix,
                                                  " of CLR Header");
          }

          // State

          internal int signature;
          // IMAGE_FILE_HEADER
          internal short machine;
          internal short numberOfSections;
          internal int   timeDateStamp;
          internal int   pointerToSymbolTable;
          internal int   numberOfSymbols;
          internal short sizeOfOptionalHeader;
          internal short characteristics;
          // IMAGE_OPTIONAL_HEADER32
          internal short magic;
          internal Byte  majorLinkerVersion;
          internal Byte  minorLinkerVersion;
          internal int   sizeOfCode;
          internal int   sizeOfInitializedData;
          internal int   sizeOfUninitializedData;
          internal int   addressOfEntryPoint;
          internal int   baseOfCode;
          internal int   baseOfData;
          internal int   imageBase;
          internal int   sectionAlignment;
          internal int   fileAlignment;
          internal short majorOperatingSystemVersion;
          internal short minorOperatingSystemVersion;
          internal short majorImageVersion;
          internal short minorImageVersion;
          internal short majorSubsystemVersion;
          internal short minorSubsystemVersion;
          internal int   win32VersionValue;
          internal int   sizeOfImage;
          internal int   sizeOfHeaders;
          internal int   checkSum;
          internal short subsystem;
          internal short dllCharacteristics;
          internal int   sizeOfStackReserve;
          internal int   sizeOfStackCommit;
          internal int   sizeOfHeapReserve;
          internal int   sizeOfHeapCommit;
          internal int   loaderFlags;
          internal int   numberOfRvaAndSizes;
          // IMAGE_DATA_DIRECTORY
          internal DirectoryEntry[] dataDirectory;

          internal const int IMAGE_NT_SIGNATURE = 0x00004550; // PE00
          internal const short IMAGE_SIZEOF_NT_OPTIONAL32_HEADER = 224;
          internal const short IMAGE_NT_OPTIONAL_HDR32_MAGIC = 0x010b;
          // File is executable  (i.e. no unresolved external references).
          internal const short IMAGE_FILE_EXECUTABLE_IMAGE = 0x0002;
          // File is a DLL.
          internal const short IMAGE_FILE_DLL = 0x2000;
      }

      internal struct DirectoryEntry {

          // How to create from a stream

          internal DirectoryEntry(Stream stream):
              this(new BinaryReader(stream))
          { }

          internal DirectoryEntry(BinaryReader reader) {
              this.virtualAddress = reader.ReadInt32();
              this.size           = reader.ReadInt32();
          }

          // Output Routines

          internal void DumpToStream(StreamWriter outputStream,
                                     String prefix,
                                     String suffix) {
              outputStream.WriteLine(prefix+
                                     this.virtualAddress.ToString("x8")+
                                     " ["+
                                     this.size.ToString("x8")+
                                     "] address [size]"+
                                     suffix);
          }

          // State

          internal int virtualAddress;
          internal int size;
      }

      public class Section {
          public Section(SectionHeader header) {
              this.header = header;
          }

          public void LoadSection(PELoader peLoader) {
              Stream fileStream = peLoader.getStream();
              fileStream.Seek(peLoader.VaToOffset(header.virtualAddress), SeekOrigin.Begin);
              BinaryReader reader = new BinaryReader(fileStream);
              this.rawData = reader.ReadBytes(header.sizeOfRawData);
          }

          public SectionHeader header;
          byte[] rawData;
      }

      public class SectionHeader {

          // How to create from a stream

          public SectionHeader(Stream stream):
              this(new BinaryReader(stream))
          { }

          public  SectionHeader(BinaryReader reader) {
              byte[] bytes = new byte[8];
              reader.Read(bytes, 0, 8);
              char[] chars = new char[8];
              for (int j = 0; j < 8; j++) {
                  chars[j] = (char) bytes[j];
              }
              this.name                         = new String(chars);
              this.virtualSize = reader.ReadInt32();
              this.virtualAddress               = reader.ReadInt32();
              this.sizeOfRawData                = reader.ReadInt32();
              this.pointerToRawData             = reader.ReadInt32();
              this.pointerToRelocations         = reader.ReadInt32();
              this.pointerToLinenumbers         = reader.ReadInt32();
              this.numberOfRelocations          = reader.ReadInt16();
              this.numberOfLinenumbers          = reader.ReadInt16();
              this.characteristics              = reader.ReadInt32();
          }

          // State

          public String name;
          public int    virtualSize;
          public int    virtualAddress;
          public int    sizeOfRawData;
          public int    pointerToRawData;
          public int    pointerToRelocations;
          public int    pointerToLinenumbers;
          public short  numberOfRelocations;
          public short  numberOfLinenumbers;
          public int    characteristics;
      }

      internal class COMHeader {
          // Corresponds to the WinNT IMAGE_COR20_HEADER data structure

          // How to create from a stream

          internal COMHeader(Stream stream):
              this(new BinaryReader(stream))
          { }

          internal COMHeader(BinaryReader reader) {
              this.cb                                     = reader.ReadInt32();
              this.majorRuntimeVersion                    = reader.ReadInt16();
              this.minorRuntimeVersion                    = reader.ReadInt16();
              this.metaData = new DirectoryEntry(reader);
              this.flags                                  = reader.ReadInt32();
              this.entryPointToken                        = reader.ReadInt32();
              this.resources = new DirectoryEntry(reader);
              this.strongNameSignature = new DirectoryEntry(reader);
              this.codeManagerTable = new DirectoryEntry(reader);
              this.vtableFixups = new DirectoryEntry(reader);
              this.exportAddressTableJumps = new DirectoryEntry(reader);
              this.managedNativeHeader = new DirectoryEntry(reader);
              // Verify that we have a valid header
              if (this.majorRuntimeVersion == 1 ||
                  this.majorRuntimeVersion > 2) {
                  throw new IllegalPEFormatException("COM header problems");
              }
          }

          // State

          // Header Versioning
          internal int            cb;
          internal short          majorRuntimeVersion;
          internal short          minorRuntimeVersion;
          // Symbol table and startup information
          internal DirectoryEntry metaData;
          internal int            flags;
          internal int            entryPointToken;
          // Binding information
          internal DirectoryEntry resources;
          internal DirectoryEntry strongNameSignature;
          // Regular fixup and binding information
          internal DirectoryEntry codeManagerTable;
          internal DirectoryEntry vtableFixups;
          internal DirectoryEntry exportAddressTableJumps;
          // Managed Native Code
          internal DirectoryEntry managedNativeHeader;

          // Index of the COM header in the array of directories
          internal const int      ENTRYINDEX = 14;
      }

      internal class ImportDescriptor {

          // How to create from a stream

          internal ImportDescriptor(Stream stream):
              this(new BinaryReader(stream))
          { }

          internal ImportDescriptor(BinaryReader reader) {
              this.characteristics = reader.ReadInt32();
              this.timeDateStamp = reader.ReadInt32();
              this.forwarderChain = reader.ReadInt32();
              this.name = reader.ReadInt32();
              this.firstChunk = reader.ReadInt32();
          }

          internal void DumpToStream(StreamWriter outputStream, String prefix) {
              outputStream.WriteLine(prefix+
                                     this.firstChunk.ToString("x8")+
                                     " Import Address Table");
              outputStream.WriteLine(prefix+
                                     this.name.ToString("x8")+
                                     " Import Name Table");
              outputStream.WriteLine(prefix+
                                     this.timeDateStamp.ToString("x8")+
                                     " time date stamp");
              outputStream.WriteLine(prefix+
                                     this.forwarderChain.ToString("x8")+
                                     " index of first forwarder reference");
          }

          // State

          internal int characteristics;
          internal int timeDateStamp;
          internal int forwarderChain;
          internal int name;
          internal int firstChunk;

          // Size of this structure in stream

          internal const int SIZE = 20;
      }

      internal class IllegalPEFormatException: Exception {

          // Constructor Methods

          internal IllegalPEFormatException(String reason):
              base(reason)
          { }

      }

      internal class NotYetImplemented: Exception {

          // Constructor Methods

          internal NotYetImplemented(String reason):
              base(reason)
          { }

      }

  }
}
