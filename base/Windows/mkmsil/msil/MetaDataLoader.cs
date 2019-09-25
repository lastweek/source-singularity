//
// Copyright (c) Microsoft Corporation.   All rights reserved.
//

// Loader of MetaData information

namespace Bartok.MSIL
{

  using System;
  using System.Collections;
  using System.IO;
  using System.Reflection;
  using System.Text;
  using Bartok.DebugInfo;

  internal class MetaDataLoader {

      // Constructor Methods

      internal static MetaData getMetaData(String name,
                                           PELoader peLoader,
                                           bool fLoadCode,
                                           bool fLoadDebugInfo)
      {
          int metaDataOffset = peLoader.getMetaDataOffset();
          Stream fileStream = peLoader.getStream();
          fileStream.Seek(metaDataOffset, SeekOrigin.Begin);
          BinaryReader reader = new BinaryReader(fileStream);
          StorageSignature storageSignature = new StorageSignature(reader);
          StorageHeader storageHeader = new StorageHeader(reader);
          // The pointer is at the first stream in the list
          MetaDataFormat format = MetaDataFormat.Invalid;
          // Lightning/Src/MD/Runtime/MDInternalDisp.cpp
          StorageStream dataStream = null;
          StorageStream stringPoolStream = null;
          StorageStream blobPoolStream = null;
          StorageStream userBlobPoolStream = null;
          StorageStream guidPoolStream = null;
          MetaDataLoader mdLoader;
          for (int i = 0; i < storageHeader.streamCount; i++) {
              StorageStream storageStream = new StorageStream(reader);
              switch (storageStream.name) {
                case StorageStream.COMPRESSED_MODEL:
                    if (format == MetaDataFormat.Invalid ||
                        format == MetaDataFormat.ICR) {
                        format = MetaDataFormat.ReadOnly;
                        dataStream = storageStream;
                    }
                    break;
                case StorageStream.ENC_MODEL:
                    if (format == MetaDataFormat.Invalid ||
                        format == MetaDataFormat.ICR) {
                        format = MetaDataFormat.ReadWrite;
                        dataStream = storageStream;
                    }
                    break;
                case StorageStream.SCHEMA:
                    if (format == MetaDataFormat.Invalid) {
                        format = MetaDataFormat.ICR;
                        dataStream = storageStream;
                    }
                    break;
                case StorageStream.STRING_POOL:
                    stringPoolStream = storageStream;
                    break;
                case StorageStream.BLOB_POOL:
                    blobPoolStream = storageStream;
                    break;
                case StorageStream.USER_BLOB_POOL:
                    userBlobPoolStream = storageStream;
                    break;
                case StorageStream.VARIANT_POOL:
                    // It doesn't look like we are using this stream, ever
                    break;
                case StorageStream.GUID_POOL:
                    guidPoolStream = storageStream;
                    break;
                default:
                    throw new IllegalMetaDataFormatException("Unknown stream name "+storageStream.name);
              }
          }
          switch (format) {
            case MetaDataFormat.Invalid:
                throw new IllegalMetaDataFormatException("No valid metadata format found");
            case MetaDataFormat.ReadOnly:
                mdLoader = new MetaDataLoader(peLoader,
                                              fileStream,
                                              metaDataOffset,
                                              dataStream,
                                              stringPoolStream,
                                              blobPoolStream,
                                              userBlobPoolStream,
                                              guidPoolStream);
                break;
            case MetaDataFormat.ReadWrite:
                throw new IllegalMetaDataFormatException("MetaDataReadWrite format on disk");
            case MetaDataFormat.ICR:
                throw new IllegalMetaDataFormatException("Cannot handle ICR metadata format");
            default:
                throw new IllegalMetaDataFormatException("Unknown format "+format);
          }

          int methodIndex = 1;
          bool dllHasDebugInfo = false;
          try {
              if (fLoadDebugInfo && fLoadCode) {
                  if (PDBLoader.OpenPdbFile(name) == 0) {
                      dllHasDebugInfo = true;
                      mdLoader.LoadDebugSymbolInfo();
                  }
              }

              foreach (MetaDataMethod method in mdLoader.methodArray) {
                  if (fLoadCode) {
                      bool methodHasDebugInfo = false;
                      int baseLineNumber = 0;
                      int lastLineNumber = 0;
                      int numOfLines = 0;
                      String srcFileName = null;

                      if (fLoadDebugInfo && dllHasDebugInfo) {
                          // load line number information from the dll.
                          int token = ((int)MetaDataTableIndices.Method <<24) | methodIndex;
                          long count;    // line number count
                          uint length;   // src file name length

                          PDBLoader.GetLineNumberCount(token,
                                                       out count,
                                                       out length);
                          if (count > 0) {
                              // there is line number infor. for this method
                              int[] lines = new int[count];
                              int[] offsets = new int[count];
                              int[] columns = new int[count];
                              StringBuilder fileName =
                                  new StringBuilder((int)length);
                              int lineCount =
                                  PDBLoader.LoadLineNumber(token,
                                                           lines,
                                                           columns,
                                                           offsets,
                                                           fileName);
                              if (lineCount != count)
                                  Console.WriteLine("Error! Reading line number" + lineCount + " " + count);

                              int baseOffset = offsets[0];
                              for (int i = 0; i < lineCount; i++) {
                                  if (lines[i] == 0xFEEFEE) {
                                      // Mask noise from the dll files
                                      if (i > 0) {
                                          lines[i] = lines[i-1];
                                          columns[i] = columns[i-1];
                                      }
                                      else if (i < (lineCount - 1)) {
                                          lines[i] = lines[i+1] - 1;
                                          columns[i] = 0;
                                      }
                                      else {
                                          Console.WriteLine("Error! No Valid lineNumber");
                                          lines[i] = 1;
                                          columns[i] = 0;
                                      }
                                  }
                                // adjust offset to be 0 based.
                                  offsets[i] -= baseOffset;
                              }

                              // load instructions
                              srcFileName = fileName.ToString();
                              method.loadInstructions(mdLoader, peLoader,
                                                      fileStream, lines, columns,
                                                      offsets, srcFileName,
                                                      lineCount);
                              baseLineNumber = lines[0] - 1;
                              lastLineNumber = lines[lineCount-1] + 1;
                              numOfLines = lineCount;
                              methodHasDebugInfo = true;
                          }
                          else {
                              method.loadInstructions(mdLoader, peLoader,
                                                      fileStream, null,
                                                      null, null, null, 0);
                          }
                      }
                      else {
                          method.loadInstructions(mdLoader, peLoader,
                                                  fileStream, null,
                                                  null, null, null, 0);
                      }
                      method.BaseLineNumber = new CVLineNumber(baseLineNumber, 0,
                                                               srcFileName);
                      method.LastLineNumber = new CVLineNumber(lastLineNumber, 0,
                                                               srcFileName);
                      method.NumOfLines = numOfLines;
                      method.SrcFileName = srcFileName;
                      method.HasDebugInfo = methodHasDebugInfo;
                  }

                  if (method.Rva == 0) {
                      method.IsEmpty = true;
                  }

                  methodIndex++;
              }
          }
          finally {
              if (dllHasDebugInfo) {
                  PDBLoader.ClosePdbFile();
              }
          }

          int entryPointToken = peLoader.getEntryPoint();
          MetaDataMethod entryPoint = (entryPointToken == 0) ? null :
              (MetaDataMethod) mdLoader.getObjectFromToken(entryPointToken);
          int imageBase = peLoader.getImageBase();
          return new MetaData(name,
                              entryPoint,
                              imageBase,
                              mdLoader.moduleArray,
                              mdLoader.typeRefArray,
                              mdLoader.typeDefArray,
                              mdLoader.fieldPtrArray,
                              mdLoader.fieldArray,
                              mdLoader.methodPtrArray,
                              mdLoader.methodArray,
                              mdLoader.paramPtrArray,
                              mdLoader.paramArray,
                              mdLoader.interfaceImplArray,
                              mdLoader.memberRefArray,
                              mdLoader.constantArray,
                              mdLoader.customAttributeArray,
                              mdLoader.fieldMarshalArray,
                              mdLoader.declSecurityArray,
                              mdLoader.classLayoutArray,
                              mdLoader.fieldLayoutArray,
                              mdLoader.standAloneSigArray,
                              mdLoader.eventMapArray,
                              mdLoader.eventPtrArray,
                              mdLoader.eventArray,
                              mdLoader.propertyMapArray,
                              mdLoader.propertyPtrArray,
                              mdLoader.propertyArray,
                              mdLoader.methodSemanticsArray,
                              mdLoader.methodImplArray,
                              mdLoader.moduleRefArray,
                              mdLoader.typeSpecArray,
                              mdLoader.implMapArray,
                              mdLoader.fieldRVAArray,
                              mdLoader.assemblyArray,
                              mdLoader.assemblyProcessorArray,
                              mdLoader.assemblyOSArray,
                              mdLoader.assemblyRefArray,
                              mdLoader.assemblyRefProcessorArray,
                              mdLoader.assemblyRefOSArray,
                              mdLoader.fileArray,
                              mdLoader.exportedTypeArray,
                              mdLoader.manifestResourceArray,
                              mdLoader.nestedClassArray,
                              mdLoader.relocationArray,
                              mdLoader.vtableFixupArray,
                              mdLoader.delayImportTable);
      }

      private void LoadDebugSymbolInfo() {
          // read in local var info
          int varCount;
          int nameLength;
          int methodCount = PDBLoader.GetMethodCount(out varCount,
                                                     out nameLength);
          int[] slots = new int[varCount];
          String[] varNames = new String[varCount];
          StringBuilder varName = new StringBuilder(nameLength);
          int slot;
          int methodToken;
          int symTable = PDBLoader.OpenSymbolTable();
          while (symTable != -1) {
              int symTag = PDBLoader.GetNextVar(out slot, out methodToken,
                                                varName);
              int count = 0;
              int lastMethod  = -1;
              int maxslot = 0;  // somehow certain locals are not in the
                                // sym table, however, they have slots,
                                // therefore slot number can be bigger than
                                // sym count
              while (symTag != (int)SymTag.SymTagEnd) {
                  if (symTag == (int) SymTag.SymTagFunction) {
                      if (lastMethod != -1) {
                          // finish last method
                          int numOfLocals = maxslot + 1;
                          if (numOfLocals < count) {
                              numOfLocals = count;
                          }
                          UpdateMethodDebugVarInfo(lastMethod,
                                                   count, slots,
                                                   numOfLocals, varNames);
                          lastMethod = -1;
                      }
                      // start current method
                      count = 0;
                      maxslot = 0;
                      lastMethod = methodToken;
                  }
                  else if (symTag == (int)SymTag.SymTagLocal) {
                      slots[count] = slot;
                      if (slot > maxslot) {
                          maxslot = slot;
                      }
                      varNames[count] = varName.ToString();
                      count++;
                  }
                  else {
                      Console.WriteLine("wrong sym tag");
                  }
                  symTag = PDBLoader.GetNextVar(out slot, out methodToken,
                                                varName);
              }
              if (lastMethod != -1) {
                  int numOfLocals = maxslot + 1;
                  if (numOfLocals < count) {
                      numOfLocals = count;
                  }
                  UpdateMethodDebugVarInfo(lastMethod,
                                           count, slots,
                                           numOfLocals, varNames);
                  lastMethod = -1;
              }
              symTable = PDBLoader.NextSymbolTable();
          }
          PDBLoader.CloseSymbolTable();
      }

      private void UpdateMethodDebugVarInfo(int token, int count,
                                            int[] slots,
                                            int numOfLocals,
                                            String[] names) {
          MetaDataMethod method =
              (MetaDataMethod) this.getObjectFromToken(token);
          String[] varNames = new String[numOfLocals];
          for (int i = 0; i < count; i++) {
              varNames[slots[i]] = names[i];
          }
          method.LocalVarNames = varNames;
      }

      private static void LoadDebugLineNumberInfo() {

      }

      private MetaDataLoader(PELoader peLoader,
                             Stream fileStream,
                             int metaDataOffset,
                             StorageStream dataStream,
                             StorageStream stringPoolStream,
                             StorageStream blobPoolStream,
                             StorageStream userBlobPoolStream,
                             StorageStream guidPoolStream)
      {
          this.peLoader           = peLoader;
          this.fileStream         = fileStream;
          this.metaDataOffset     = metaDataOffset;
          this.dataStream         = dataStream;
          this.stringPoolStream   = stringPoolStream;
          this.blobPoolStream     = blobPoolStream;
          this.userBlobPoolStream = userBlobPoolStream;
          this.guidPoolStream     = guidPoolStream;
          // Read the stream of GUIDs
          int guidCount = guidPoolStream.size / 16;
          fileStream.Seek(metaDataOffset + guidPoolStream.offset,
                          SeekOrigin.Begin);
          this.guidArray = new Guid[guidCount];
          byte[] guidBuffer = new byte[16];
          for (int i = 0; i < guidCount; i++) {
              fileStream.Read(guidBuffer, 0, 16);
              guidArray[i] = new Guid(guidBuffer);
          }
          // Read the stream of strings
          // Ensure that last byte is always zero
          if (stringPoolStream != null && stringPoolStream.size > 0) {
              this.stringStreamBuffer = new byte[stringPoolStream.size+1];
              fileStream.Seek(metaDataOffset + stringPoolStream.offset,
                              SeekOrigin.Begin);
              int stringByteCount = fileStream.Read(this.stringStreamBuffer, 0,
                                                    stringPoolStream.size);
              if (stringByteCount != stringPoolStream.size) {
                  throw new IllegalMetaDataFormatException("Didn't get all the string bytes");
              }
          }
          // Read the stream of blobs
          if (blobPoolStream != null && blobPoolStream.size > 0) {
              this.blobStreamBuffer = new byte[blobPoolStream.size];
              fileStream.Seek(metaDataOffset + blobPoolStream.offset,
                              SeekOrigin.Begin);
              int blobByteCount = fileStream.Read(this.blobStreamBuffer, 0,
                                                  blobPoolStream.size);
              if (blobByteCount != blobPoolStream.size) {
                  throw new IllegalMetaDataFormatException("Didn't get all the blob bytes");
              }
          }
          // Read the stream of user strings, if there is one
          if (userBlobPoolStream != null && userBlobPoolStream.size > 0) {
              this.userStringStreamBuffer = new byte[userBlobPoolStream.size];
              fileStream.Seek(metaDataOffset + userBlobPoolStream.offset,
                              SeekOrigin.Begin);
              int userStringByteCount =
                  fileStream.Read(this.userStringStreamBuffer, 0,
                                  userBlobPoolStream.size);
              if (userStringByteCount != userBlobPoolStream.size) {
                  throw new IllegalMetaDataFormatException("Didn't get all the user string bytes");
              }
          }
          // Read the resource data, if there is any
          int resourceOffset = peLoader.getResourceOffset();
          int resourceSize = peLoader.getResourceSize();
          if (resourceOffset > 0 && resourceSize > 0) {
              this.resourceBuffer = new byte[resourceSize];
              fileStream.Seek(resourceOffset, SeekOrigin.Begin);
              int resourceCount =
                  fileStream.Read(this.resourceBuffer, 0, resourceSize);
              if (resourceCount != resourceSize) {
                  throw new IllegalMetaDataFormatException("Didn't get all the resource bytes");
              }
          }
          // Read the schema
          fileStream.Seek(metaDataOffset + dataStream.offset,
                          SeekOrigin.Begin);
          BinaryReader reader = new BinaryReader(fileStream);
          // First read the fixed fields (CMiniMdSchemaBase)
          this.ReadSchemaBase(reader);
          int readBytes = 24;   // sizeof(CMiniMDSchemaBase)
          // Read the variable fields (this is the compressed part)
          int count = (int) MetaDataTableIndices.Count;
          long mask = this.maskValid;
          for (int dst = 0; dst < count; dst++) {
              if ((mask & 1) != 0) {
                  this.countArray[dst] = reader.ReadInt32();
                  readBytes += 4;
              }
              mask >>= 1;
          }
          // Skip the counters we don't understand
          for (int dst = count; dst < 64; dst++) {
              if ((mask & 1) != 0) {
                  reader.ReadInt32();
                  readBytes += 4;
              }
          }
          // Retrieve any extra data
          if ((this.heapBits & HEAPBITS_MASK_EXTRA_DATA) != 0) {
              this.extraData = reader.ReadInt32();
              readBytes += 4;
          }
          if (this.majorVersion != METAMODEL_MAJOR_VER ||
              (this.minorVersion != METAMODEL_MINOR_VER_A
               && this.minorVersion != METAMODEL_MINOR_VER_B)) {
              throw new IllegalMetaDataFormatException("Unknown version "+this.majorVersion+"."+this.minorVersion);
          }
          if (this.countArray[(int) MetaDataTableIndices.MethodPtr] != 0 ||
              this.countArray[(int) MetaDataTableIndices.FieldPtr] != 0) {
              throw new IllegalMetaDataFormatException("Trying to open R/W format at R/O");
          }
          // Read the data into the tables
          int tableSize = this.InitializeRowInfo();
          if (readBytes + tableSize > dataStream.size) {
              throw new IllegalMetaDataFormatException("Table bigger than metadata stream");
          }

          this.InitializeMetaDataTables(reader);
      }

      // Helper Methods

      private void ReadSchemaBase(BinaryReader reader) {
          this.reserved     = reader.ReadInt32(); // Must be zero
          this.majorVersion = reader.ReadByte();  //  Version numbers
          this.minorVersion = reader.ReadByte();
          this.heapBits     = reader.ReadByte();  // Bits for heap sizes
          this.rowId        = reader.ReadByte();  // log-base-2 of largest rid
          this.maskValid    = reader.ReadInt64(); // Present table counts
          this.maskSorted   = reader.ReadInt64(); // Sorted tables
          if (this.reserved != 0) {
              throw new IllegalMetaDataFormatException("Reserved not zero");
          }
      }

      private int InitializeRowInfo() {
          if ((this.heapBits & HEAPBITS_MASK_STRINGS) != 0) {
              this.stringIndexSize = 4;
          }
          else {
              this.stringIndexSize = 2;
          }
          if ((this.heapBits & HEAPBITS_MASK_GUID) != 0) {
              this.guidIndexSize = 4;
          }
          else {
              this.guidIndexSize = 2;
          }
          if ((this.heapBits & HEAPBITS_MASK_BLOB) != 0) {
              this.blobIndexSize = 4;
          }
          else {
              this.blobIndexSize = 2;
          }
          int tableSize = 0;
          for (int tableIndex = 0; tableIndex < (int) MetaDataTableIndices.Count; tableIndex++) {
              byte[] columnKinds = TableColumnKinds[tableIndex];
              int columnCount = columnKinds.Length;
              byte[] columnSizes = new byte[columnCount];
              byte[] columnOffsets = new byte[columnCount];
              this.tableColumnSizes[tableIndex] = columnSizes;
              this.tableColumnOffsets[tableIndex] = columnOffsets;
              byte columnOffset = 0;  // Running size of record
              for (int columnIndex = 0; columnIndex < columnCount; columnIndex++) {
                  byte columnKind = columnKinds[columnIndex];
                  byte columnSize;
                  if (columnKind <= (byte) ColumnKindId.RowIdMax) {
                      if (this.countArray[columnKind] > 0xffff) {
                          columnSize = 4;
                      }
                      else {
                          columnSize = 2;
                      }
                  }
                  else if (columnKind <= (byte) ColumnKindId.CodedTokenMax) {
                      byte codeToken = (byte)
                          (columnKind - (byte) ColumnKindId.CodedToken);
                      TokenType[] tokenTypeList =
                          CodeTokenTypeLists[codeToken];
                      int maxCount = 0;
                      int listLength = tokenTypeList.Length;
                      for (int i = 0; i < listLength; i++) {
                          TokenType tokenType = tokenTypeList[i];
                          // Ignore string tokens
                          if (tokenType != TokenType.String) {
                              int index = ((int) tokenType >> 24);
                              if (this.countArray[index] > maxCount) {
                                  maxCount = this.countArray[index];
                              }
                          }
                      }
                      int maxIndex = maxCount << BitsForCountArray[listLength];
                      if (maxIndex > 0xffff) {
                          columnSize = 4;
                      }
                      else {
                          columnSize = 2;
                      }
                  }
                  else {
                      switch ((ColumnKindId) columnKind) {
                        case ColumnKindId.Byte:
                            columnSize = 1;
                            break;
                        case ColumnKindId.Short:
                        case ColumnKindId.UShort:
                            columnSize = 2;
                            break;
                        case ColumnKindId.Long:
                        case ColumnKindId.ULong:
                            columnSize = 4;
                            break;
                        case ColumnKindId.String:
                            columnSize = this.stringIndexSize;
                            break;
                        case ColumnKindId.Guid:
                            columnSize = this.guidIndexSize;
                            break;
                        case ColumnKindId.Blob:
                            columnSize = this.blobIndexSize;
                            break;
                        default:
                            throw new IllegalMetaDataFormatException("Unexpected schema kind: "+columnKind);
                      }
                  }
                  // Save away the size and offset
                  columnSizes[columnIndex] = columnSize;
                  columnOffsets[columnIndex] = columnOffset;
                  // Align to 2 bytes
                  columnSize += (byte) (columnSize & 1);
                  columnOffset += columnSize;
              }
              this.tableRowSizes[tableIndex] = columnOffset;
              tableSize += columnOffset * this.countArray[tableIndex];
          }
          return tableSize;
      }

      private String getString(int stringIndex) {
          int limit = this.stringStreamBuffer.Length;
          if (stringIndex < 0 || stringIndex >= limit) {
              Console.WriteLine("Cannot find string "+stringIndex);
              return null;
          }
          else {
              int endIndex = stringIndex;
              while (this.stringStreamBuffer[endIndex] != 0) {
                  endIndex++;
              }
              return stringEncoding.GetString(this.stringStreamBuffer,
                                              stringIndex,
                                              endIndex - stringIndex);
          }
      }

      private byte[] getBlobBytes(int blobIndex) {
          byte headerByte = this.blobStreamBuffer[blobIndex];
          int size, startIndex;
          if ((headerByte & 0x80) == 0x00) {
              size = headerByte;
              startIndex = blobIndex+1;
          }
          else if ((headerByte & 0x40) == 0x00) {
              size = (((headerByte & 0x3f) << 8) |
                      this.blobStreamBuffer[blobIndex+1]);
              startIndex = blobIndex+2;
          }
          else {
              size = (((headerByte & 0x3f) << 24) |
                      (this.blobStreamBuffer[blobIndex+1] << 16) |
                      (this.blobStreamBuffer[blobIndex+2] << 8) |
                      (this.blobStreamBuffer[blobIndex+3]));
              startIndex = blobIndex+4;
          }
          byte[] buffer = new byte[size];
          System.Array.Copy(this.blobStreamBuffer, startIndex,
                            buffer, 0, size);
          return buffer;
      }

      private byte[] getResourceBytes(int offset) {
          int size = ((this.resourceBuffer[offset]) |
                      (this.resourceBuffer[offset+1] << 8) |
                      (this.resourceBuffer[offset+2] << 16) |
                      (this.resourceBuffer[offset+3] << 24));
          byte[] buffer = new byte[size];
          System.Array.Copy(this.resourceBuffer, offset+4, buffer, 0, size);
          return buffer;
      }

      private Signature getSignature(int signatureIndex) {
          byte[] buffer = this.getBlobBytes(signatureIndex);
          return new SignatureBuffer(buffer);
      }

      private byte[] getValueBuffer(int valueIndex) {
          return this.getBlobBytes(valueIndex);
      }

      private MarshalSpec getNativeType(int nativeTypeIndex) {
          byte[] buffer = this.getBlobBytes(nativeTypeIndex);
          return MarshalSpec.Create(buffer);
      }

      private byte[] getPublicKey(int publicKeyIndex) {
          return this.getBlobBytes(publicKeyIndex);
      }

      private MetaDataBlob getPermissionSet(int permissionSetIndex) {
          // BUGBUG
          return new MetaDataBlob(this.getBlobBytes(permissionSetIndex));
      }

      private byte[] getHashValue(int hashValueIndex) {
          return this.getBlobBytes(hashValueIndex);
      }

      private Guid getGuid(int guidIndex) {
          if (guidIndex < 0 || guidIndex >= this.guidArray.Length) {
              Console.WriteLine("Cannot find GUID "+guidIndex);
              return Guid.Empty;
          }
          else {
              return this.guidArray[guidIndex];
          }
      }

      private MetaDataObject getObjectFromTableSet(int codedIndex,
                                                   CodeToken codeToken) {
          if (codedIndex == 0) {
              return null;
          }
          int codeCount = CodeTokenTypeLists[(int) codeToken].Length;
          int kind = codedIndex & MaskForCountArray[codeCount];
          int index = codedIndex >> BitsForCountArray[codeCount];
          TokenType tokenType = CodeTokenTypeLists[(int) codeToken][kind];
          MetaDataObject[] array = this.metaDataTable[(int) tokenType >> 24];

          if (array == null) {
              Console.WriteLine("Missing table for kind "+kind+" of "+codeToken);
              return null;
          }
          else {
              return array[index-1];
          }
      }

      private void InitializeMetaDataTables(BinaryReader reader) {
          this.metaDataTable =
              new MetaDataObject[(int) MetaDataTableIndices.Count][];
          // First read in what goes in the tables
          this.initializeModuleTable(reader);
          this.initializeTypeRefTable(reader);
          this.initializeTypeDefTable(reader);
          this.initializeFieldPtrTable(reader);
          this.initializeFieldTable(reader);
          this.initializeMethodPtrTable(reader);
          this.initializeMethodTable(reader);
          this.initializeParamPtrTable(reader);
          this.initializeParamTable(reader);
          this.initializeInterfaceImplTable(reader);
          this.initializeMemberRefTable(reader);
          this.initializeConstantTable(reader);
          this.initializeCustomAttributeTable(reader);
          this.initializeFieldMarshalTable(reader);
          this.initializeDeclSecurityTable(reader);
          this.initializeClassLayoutTable(reader);
          this.initializeFieldLayoutTable(reader);
          this.initializeStandAloneSigTable(reader);
          this.initializeEventMapTable(reader);
          this.initializeEventPtrTable(reader);
          this.initializeEventTable(reader);
          this.initializePropertyMapTable(reader);
          this.initializePropertyPtrTable(reader);
          this.initializePropertyTable(reader);
          this.initializeMethodSemanticsTable(reader);
          this.initializeMethodImplTable(reader);
          this.initializeModuleRefTable(reader);
          this.initializeTypeSpecTable(reader);
          this.initializeImplMapTable(reader);
          this.initializeFieldRVATable(reader);
          this.initializeENCLogTable(reader);
          this.initializeENCMapTable(reader);
          this.initializeAssemblyTable(reader);
          this.initializeAssemblyProcessorTable(reader);
          this.initializeAssemblyOSTable(reader);
          this.initializeAssemblyRefTable(reader);
          this.initializeAssemblyRefProcessorTable(reader);
          this.initializeAssemblyRefOSTable(reader);
          this.initializeFileTable(reader);
          this.initializeExportedTypeTable(reader);
          this.initializeManifestResourceTable(reader);
          this.initializeNestedClassTable(reader);
          this.initializeGenericParamTable(reader);
          this.initializeMethodSpecTable(reader);
          this.initializeGenericParamConstraintTable(reader);
          this.initializeRelocationTable();
          this.initializeVtableFixupTable();
          this.initializeDelayIATTable();
          // Then resolve references between tables
          this.resolveModuleReferences();
          this.resolveTypeRefReferences();
          this.resolveTypeDefReferences();
          this.resolveFieldPtrReferences();
          this.resolveFieldReferences();
          this.resolveMethodPtrReferences();
          this.resolveMethodReferences();
          this.resolveParamPtrReferences();
          this.resolveParamReferences();
          this.resolveInterfaceImplReferences();
          this.resolveMemberRefReferences();
          this.resolveConstantReferences();
          this.resolveCustomAttributeReferences();
          this.resolveFieldMarshalReferences();
          this.resolveDeclSecurityReferences();
          this.resolveClassLayoutReferences();
          this.resolveFieldLayoutReferences();
          this.resolveStandAloneSigReferences();
          this.resolveEventMapReferences();
          this.resolveEventPtrReferences();
          this.resolveEventReferences();
          this.resolvePropertyMapReferences();
          this.resolvePropertyPtrReferences();
          this.resolvePropertyReferences();
          this.resolveMethodSemanticsReferences();
          this.resolveMethodImplReferences();
          this.resolveModuleRefReferences();
          this.resolveTypeSpecReferences();
          this.resolveImplMapReferences();
          this.resolveFieldRVAReferences();
          this.resolveENCLogReferences();
          this.resolveENCMapReferences();
          this.resolveAssemblyReferences();
          this.resolveAssemblyProcessorReferences();
          this.resolveAssemblyOSReferences();
          this.resolveAssemblyRefReferences();
          this.resolveAssemblyRefProcessorReferences();
          this.resolveAssemblyRefOSReferences();
          this.resolveFileReferences();
          this.resolveExportedTypeReferences();
          this.resolveManifestResourceReferences();
          this.resolveNestedClassReferences();
          this.resolveGenericParamReferences();
          this.resolveMethodSpecReferences();
          this.resolveGenericParamConstraintReferences();
      }

      private void initializeModuleTable(BinaryReader reader) {
          int count = this.countArray[(int) MetaDataTableIndices.Module];
          this.moduleArray = new MetaDataModule[count];
          this.metaDataTable[(int) MetaDataTableIndices.Module] =
              this.moduleArray;
          for (int i = 0; i < count; i++) {
              short generation = reader.ReadInt16();
              int nameIndex, mvid, encodingIndex, encodingBaseIdIndex;
              if (this.stringIndexSize == 4) {
                  nameIndex = reader.ReadInt32();
              }
              else {
                  nameIndex = reader.ReadUInt16();
              }
              String name = this.getString(nameIndex);
              if (this.guidIndexSize == 4) {
                  mvid = reader.ReadInt32();
                  encodingIndex = reader.ReadInt32();
                  encodingBaseIdIndex = reader.ReadInt32();
              }
              else {
                  mvid = reader.ReadUInt16();
                  encodingIndex = reader.ReadUInt16();
                  encodingBaseIdIndex = reader.ReadUInt16();
              }
              Guid encoding = this.getGuid(encodingIndex);
              Guid encodingBaseId = this.getGuid(encodingBaseIdIndex);
              this.moduleArray[i] =
                  new MetaDataModule(generation, name, mvid,
                                     encodingIndex, encoding,
                                     encodingBaseIdIndex, encodingBaseId);
          }
      }

      // Access Methods

      internal String getUserString(int stringIndex) {
          byte headerByte = this.userStringStreamBuffer[stringIndex];
          int size, startIndex;
          if ((headerByte & 0x80) == 0x00) {
              size = headerByte;
              startIndex = stringIndex + 1;
          }
          else if ((headerByte & 0x40) == 0x00) {
              size = (((headerByte & 0x3f) << 8) |
                      this.userStringStreamBuffer[stringIndex + 1]);
              startIndex = stringIndex + 2;
          }
          else {
              size = (((headerByte & 0x3f) << 24) |
                      (this.userStringStreamBuffer[stringIndex+1] << 16) |
                      (this.userStringStreamBuffer[stringIndex+2] << 8) |
                      (this.userStringStreamBuffer[stringIndex+3]));
              startIndex = stringIndex+4;
          }
          int stringSize = size/2;
          char[] chars = new char[stringSize];
          for (int i = 0; i < stringSize; i++) {
              char ch =
                  (char ) (this.userStringStreamBuffer[startIndex] |
                           this.userStringStreamBuffer[startIndex+1] << 8);
              chars[i] = ch;
              startIndex += 2;
          }
          return new String(chars);
      }

      internal MetaDataObject getTypeDefOrRef(int codedIndex) {
          return this.getObjectFromTableSet(codedIndex,
                                            CodeToken.TypeDefOrRef);
      }

      internal MetaDataObject getHasConstant(int codedIndex) {
          return this.getObjectFromTableSet(codedIndex,
                                            CodeToken.HasConstant);
      }

      internal MetaDataObject getHasCustomAttribute(int codedIndex) {
          return this.getObjectFromTableSet(codedIndex,
                                            CodeToken.HasCustomAttribute);
      }

      internal MetaDataObject getHasFieldMarshal(int codedIndex) {
          return this.getObjectFromTableSet(codedIndex,
                                            CodeToken.HasFieldMarshal);
      }

      internal MetaDataObject getHasDeclSecurity(int codedIndex) {
          return this.getObjectFromTableSet(codedIndex,
                                            CodeToken.HasDeclSecurity);
      }

      internal MetaDataObject getMemberRefParent(int codedIndex) {
          return this.getObjectFromTableSet(codedIndex,
                                            CodeToken.MemberRefParent);
      }

      internal MetaDataObject getHasSemantic(int codedIndex) {
          return this.getObjectFromTableSet(codedIndex,
                                            CodeToken.HasSemantic);
      }

      internal MetaDataObject getMethodDefOrRef(int codedIndex) {
          return this.getObjectFromTableSet(codedIndex,
                                            CodeToken.MethodDefOrRef);
      }

      internal MetaDataObject getMemberForwarded(int codedIndex) {
          return this.getObjectFromTableSet(codedIndex,
                                            CodeToken.MemberForwarded);
      }

      internal MetaDataObject getImplementation(int codedIndex) {
          return this.getObjectFromTableSet(codedIndex,
                                            CodeToken.Implementation);
      }

      internal MetaDataObject getCustomAttributeType(int codedIndex) {
          return this.getObjectFromTableSet(codedIndex,
                                            CodeToken.CustomAttributeType);
      }

      internal MetaDataObject getResolutionScope(int resolutionIndex) {
          return this.getObjectFromTableSet(resolutionIndex,
                                            CodeToken.ResolutionScope);
      }

      internal MetaDataObject getTypeOrMethodDef(int resolutionIndex) {
          return this.getObjectFromTableSet(resolutionIndex,
                                            CodeToken.TypeOrMethodDef);
      }

      internal MetaDataObject getObjectFromToken(int token) {
          int type = token >> 24;
          int index = token & 0x00FFFFFF;
          return this.metaDataTable[type][index-1];
      }

      internal MetaDataTypeDefinition getTypeDef(int typeDefIndex) {
          if (typeDefIndex < 1 || typeDefIndex > this.typeDefArray.Length) {
              Console.WriteLine("Cannot find TypeDef "+typeDefIndex);
              return null;
          }
          else {
              return this.typeDefArray[typeDefIndex-1];
          }
      }

      internal MetaDataField getField(int fieldIndex) {
          if (fieldIndex < 1 || fieldIndex > this.fieldArray.Length) {
              Console.WriteLine("Cannot find field "+fieldIndex);
              return null;
          }
          else {
              return this.fieldArray[fieldIndex-1];
          }
      }

      internal MetaDataField[] getFields(int startIndex, int count) {
          if (count <= 0) {
              return emptyFieldArray;
          }
          MetaDataField[] result = new MetaDataField[count];
          Array.Copy(this.fieldArray, startIndex-1, result, 0, count);
          return result;
      }

      internal MetaDataMethod getMethod(int methodIndex) {
          if (methodIndex < 1 || methodIndex > this.methodArray.Length) {
              Console.WriteLine("Cannot find method "+methodIndex);
              return null;
          }
          else {
              return this.methodArray[methodIndex-1];
          }
      }

      internal MetaDataMethod[] getMethods(int startIndex, int count) {
          if (count <= 0) {
              return emptyMethodArray;
          }
          MetaDataMethod[] result = new MetaDataMethod[count];
          Array.Copy(this.methodArray, startIndex-1, result, 0, count);
          return result;
      }

      internal MetaDataParam getParam(int paramIndex) {
          if (paramIndex < 1 || paramIndex > this.paramArray.Length) {
              Console.WriteLine("Cannot find parameter "+paramIndex);
              return null;
          }
          else {
              return this.paramArray[paramIndex-1];
          }
      }

      internal MetaDataParam[] getParams(int startIndex, int count) {
          if (count <= 0) {
              return emptyParamArray;
          }
          if (startIndex < this.paramArray.Length &&
              this.getParam(startIndex).Sequence == 0) {
              startIndex++;
              count--;
          }
          for (int i = 0; i < count; i++) {
              if (startIndex + i < this.paramArray.Length) {
                  if (this.getParam(startIndex + i).Sequence == 0) {
                      throw new Exception("Asking for non-owned parameters");
                  }
              }
          }
          MetaDataParam[] result = new MetaDataParam[count];
          Array.Copy(this.paramArray, startIndex-1, result, 0, count);
          return result;
      }

      internal MetaDataEvent getEvent(int eventIndex) {
          if (eventIndex < 1 || eventIndex > this.eventArray.Length) {
              Console.WriteLine("Cannot find event "+eventIndex);
              return null;
          }
          else {
              return this.eventArray[eventIndex-1];
          }
      }

      internal MetaDataProperty getProperty(int propertyIndex) {
          if (propertyIndex < 1 || propertyIndex > this.propertyArray.Length) {
              Console.WriteLine("Cannot find property "+propertyIndex);
              return null;
          }
          else {
              return this.propertyArray[propertyIndex-1];
          }
      }

      internal MetaDataModuleRef getModuleRef(int moduleRefIndex) {
          if (moduleRefIndex < 1 ||
              moduleRefIndex > this.moduleRefArray.Length) {
              Console.WriteLine("Cannot find moduleref "+moduleRefIndex);
              return null;
          }
          else {
              return this.moduleRefArray[moduleRefIndex-1];
          }
      }

      internal MetaDataAssemblyRef getAssemblyRef(int assemblyRefIndex) {
          if (assemblyRefIndex < 1 ||
              assemblyRefIndex > this.assemblyRefArray.Length) {
              Console.WriteLine("Cannot find assemblyref "+assemblyRefIndex);
              return null;
          }
          else {
              return this.assemblyRefArray[assemblyRefIndex-1];
          }
      }

      internal MetaDataGenericParam getGenericParam(int genericParamIndex) {
          if (genericParamIndex < 1 ||
              genericParamIndex > this.genericParamArray.Length) {
              Console.WriteLine("Cannot find genericparam "+genericParamIndex);
              return null;
          }
          return this.genericParamArray[genericParamIndex-1];
      }

      // Methods for initializing the tables and table objects

      private void resolveModuleReferences() {
//            foreach (MetaDataModule module in this.moduleArray) {
//                Console.WriteLine(module.ToStringLong());
//            }
      }

      private void initializeTypeRefTable(BinaryReader reader) {
          int count = this.countArray[(int) MetaDataTableIndices.TypeRef];
          this.typeRefArray = new MetaDataTypeReference[count];
          this.metaDataTable[(int) MetaDataTableIndices.TypeRef] =
              this.typeRefArray;
          byte bigScopeIndexSize =
              this.tableColumnSizes[(int)MetaDataTableIndices.TypeRef][0];
          for (int i = 0; i < count; i++) {
              int resolutionScopeIndex = ((bigScopeIndexSize == 4) ?
                                          reader.ReadInt32() :
                                          reader.ReadUInt16());
              int nameIndex, nameSpaceIndex;
              if (this.stringIndexSize == 4) {
                  nameIndex = reader.ReadInt32();
                  nameSpaceIndex = reader.ReadInt32();
              }
              else {
                  nameIndex = reader.ReadUInt16();
                  nameSpaceIndex = reader.ReadUInt16();
              }
              String name = this.getString(nameIndex);
              String nameSpace = this.getString(nameSpaceIndex);
              this.typeRefArray[i] =
                  new MetaDataTypeReference(resolutionScopeIndex,
                                            name, nameSpace);
          }
      }

      private void resolveTypeRefReferences() {
          foreach (MetaDataTypeReference typeRef in this.typeRefArray) {
              typeRef.resolveReferences(this);
//                Console.WriteLine(typeRef.ToStringLong());
          }
      }

      private void initializeTypeDefTable(BinaryReader reader) {
          int count = this.countArray[(int) MetaDataTableIndices.TypeDef];
          this.typeDefArray = new MetaDataTypeDefinition[count];
          this.metaDataTable[(int) MetaDataTableIndices.TypeDef] =
              this.typeDefArray;
          byte extendsSize =
              this.tableColumnSizes[(int)MetaDataTableIndices.TypeDef][3];
          byte fieldSize =
              this.tableColumnSizes[(int)MetaDataTableIndices.TypeDef][4];
          byte methodSize =
              this.tableColumnSizes[(int)MetaDataTableIndices.TypeDef][5];
          for (int i = 0; i < count; i++) {
              TypeAttributes flags = (TypeAttributes) reader.ReadInt32();
              int nameIndex, nameSpaceIndex;
              if (this.stringIndexSize == 4) {
                  nameIndex = reader.ReadInt32();
                  nameSpaceIndex = reader.ReadInt32();
              }
              else {
                  nameIndex = reader.ReadUInt16();
                  nameSpaceIndex = reader.ReadUInt16();
              }
              String name = this.getString(nameIndex);
              String nameSpace = this.getString(nameSpaceIndex);
              int extendsIndex = ((extendsSize == 4) ?
                                  reader.ReadInt32() :
                                  reader.ReadUInt16());
              int fieldIndex = ((fieldSize == 4) ?
                                reader.ReadInt32() :
                                reader.ReadUInt16());
              int methodIndex = ((methodSize == 4) ?
                                 reader.ReadInt32() :
                                 reader.ReadUInt16());
              this.typeDefArray[i] =
                  new MetaDataTypeDefinition(flags, name, nameSpace,
                                             extendsIndex, fieldIndex,
                                             methodIndex);
          }
      }

      private void resolveTypeDefReferences() {
          int fieldCount = this.fieldArray.Length;
          int methodCount = this.methodArray.Length;
          MetaDataTypeDefinition[] fieldOwners =
              new MetaDataTypeDefinition[fieldCount+2];
          MetaDataTypeDefinition[] methodOwners =
              new MetaDataTypeDefinition[methodCount+2];
          foreach (MetaDataTypeDefinition typedef in this.typeDefArray) {
              typedef.registerReferences(fieldCount, methodCount,
                                         fieldOwners, methodOwners);
          }
          MetaDataTypeDefinition current = null;
          for (int i = 0; i <= fieldCount; i++) {
              if (fieldOwners[i] == null) {
                  fieldOwners[i] = current;
              }
              else {
                  current = fieldOwners[i];
              }
          }
          current = null;
          for (int i = 0; i <= methodCount; i++) {
              if (methodOwners[i] == null) {
                  methodOwners[i] = current;
              }
              else {
                  current = methodOwners[i];
              }
          }
          foreach (MetaDataTypeDefinition typedef in this.typeDefArray) {
              typedef.resolveReferences(this, fieldOwners, methodOwners);
          }
      }

      private void initializeFieldPtrTable(BinaryReader reader) {
          int count = this.countArray[(int) MetaDataTableIndices.FieldPtr];
          this.fieldPtrArray = new MetaDataFieldPtr[count];
          this.metaDataTable[(int) MetaDataTableIndices.FieldPtr] =
              this.fieldPtrArray;
          byte indexSize =
              this.tableColumnSizes[(int)MetaDataTableIndices.FieldPtr][0];
          for (int i = 0; i < count; i++) {
              int fieldIndex = ((indexSize == 4) ?
                                reader.ReadInt32() :
                                reader.ReadUInt16());
              this.fieldPtrArray[i] = new MetaDataFieldPtr(fieldIndex);
          }
      }

      private void resolveFieldPtrReferences() {
          foreach (MetaDataFieldPtr fieldPtr in this.fieldPtrArray) {
              fieldPtr.resolveReferences(this);
//                Console.WriteLine(fieldPtr);
          }
      }

      private void initializeFieldTable(BinaryReader reader) {
          int count = this.countArray[(int) MetaDataTableIndices.Field];
          this.fieldArray = new MetaDataField[count];
          this.metaDataTable[(int) MetaDataTableIndices.Field] =
              this.fieldArray;
          for (int i = 0; i < count; i++) {
              short flags = reader.ReadInt16();
              int nameIndex = ((this.stringIndexSize == 4) ?
                               reader.ReadInt32() :
                               reader.ReadUInt16());
              String name = this.getString(nameIndex);
              int signatureIndex = ((this.blobIndexSize == 4) ?
                                    reader.ReadInt32() :
                                    reader.ReadUInt16());
              Signature signature = this.getSignature(signatureIndex);
              this.fieldArray[i] = new MetaDataField(flags, name, signature);
          }
      }

      private void resolveFieldReferences() {
          foreach (MetaDataField field in this.fieldArray) {
              field.resolveReferences(this);
              // Console.WriteLine(field.ToStringLong());
          }
      }

      private void initializeMethodPtrTable(BinaryReader reader) {
          int count = this.countArray[(int) MetaDataTableIndices.MethodPtr];
          this.methodPtrArray = new MetaDataMethodPtr[count];
          this.metaDataTable[(int) MetaDataTableIndices.MethodPtr] =
              this.methodPtrArray;
          byte indexSize =
              this.tableColumnSizes[(int)MetaDataTableIndices.MethodPtr][0];
          for (int i = 0; i < count; i++) {
              int methodIndex = ((indexSize == 4) ?
                                 reader.ReadInt32() :
                                 reader.ReadUInt16());
              this.methodPtrArray[i] = new MetaDataMethodPtr(methodIndex);
          }
      }

      private void resolveMethodPtrReferences() {
          foreach (MetaDataMethodPtr methodPtr in this.methodPtrArray) {
              methodPtr.resolveReferences(this);
//                Console.WriteLine(methodPtr.ToStringLong());
          }
      }

      private void initializeMethodTable(BinaryReader reader) {
          int count = this.countArray[(int) MetaDataTableIndices.Method];
          this.methodArray = new MetaDataMethod[count];
          this.metaDataTable[(int) MetaDataTableIndices.Method] =
              this.methodArray;
          byte paramSize =
              this.tableColumnSizes[(int)MetaDataTableIndices.Method][5];
          for (int i = 0; i < count; i++) {
              int rva = reader.ReadInt32();
              short implFlags = reader.ReadInt16();
              short flags = reader.ReadInt16();
              int nameIndex = ((this.stringIndexSize == 4) ?
                               reader.ReadInt32() :
                               reader.ReadUInt16());
              String name = this.getString(nameIndex);
              int signatureIndex = ((this.blobIndexSize == 4) ?
                                    reader.ReadInt32() :
                                    reader.ReadUInt16());
              Signature signature = this.getSignature(signatureIndex);
              int paramIndex = ((paramSize == 4) ?
                                reader.ReadInt32() :
                                reader.ReadUInt16());
              this.methodArray[i] =
                  new MetaDataMethod(rva, implFlags, flags, name,
                                     signature, paramIndex);
          }
      }

      private void resolveMethodReferences() {
          int paramCount = this.paramArray.Length;
          MetaDataMethod[] paramOwners = new MetaDataMethod[paramCount+2];
          foreach (MetaDataMethod method in this.methodArray) {
              method.registerReferences(paramCount, paramOwners);
          }
          MetaDataMethod current = null;
          for (int i = 1; i <= paramCount; i++) {
              if (paramOwners[i] == null) {
                  paramOwners[i] = current;
              }
              else {
                  current = paramOwners[i];
              }
          }
          foreach (MetaDataMethod method in this.methodArray) {
              method.resolveReferences(this, paramOwners);
              // Console.WriteLine(method.ToStringLong());
          }
      }

      private void initializeParamPtrTable(BinaryReader reader) {
          int count = this.countArray[(int) MetaDataTableIndices.ParamPtr];
          this.paramPtrArray = new MetaDataParamPtr[count];
          this.metaDataTable[(int) MetaDataTableIndices.ParamPtr] =
              this.paramPtrArray;
          byte indexSize =
              this.tableColumnSizes[(int)MetaDataTableIndices.ParamPtr][0];
          for (int i = 0; i < count; i++) {
              int paramIndex = ((indexSize == 4) ?
                                reader.ReadInt32() :
                                reader.ReadUInt16());
              this.paramPtrArray[i] = new MetaDataParamPtr(paramIndex);
          }
      }

      private void resolveParamPtrReferences() {
          foreach (MetaDataParamPtr paramPtr in this.paramPtrArray) {
              paramPtr.resolveReferences(this);
//                Console.WriteLine(paramPtr.ToStringLong());
          }
      }

      private void initializeParamTable(BinaryReader reader) {
          int count = this.countArray[(int) MetaDataTableIndices.Param];
          this.paramArray = new MetaDataParam[count];
          this.metaDataTable[(int) MetaDataTableIndices.Param] =
              this.paramArray;
          for (int i = 0; i < count; i++) {
              short flags = reader.ReadInt16();
              short sequence = reader.ReadInt16();
              int nameIndex = ((this.stringIndexSize == 4) ?
                               reader.ReadInt32() :
                               reader.ReadUInt16());
              String name = this.getString(nameIndex);
              this.paramArray[i] = new MetaDataParam(flags, sequence, name);
          }
      }

      private void resolveParamReferences() {
//            foreach (MetaDataParam param in this.paramArray) {
//                Console.WriteLine(param.ToStringLong());
//            }
      }

      private void initializeInterfaceImplTable(BinaryReader reader) {
          int count =
              this.countArray[(int) MetaDataTableIndices.InterfaceImpl];
          this.interfaceImplArray = new MetaDataInterfaceImpl[count];
          this.metaDataTable[(int) MetaDataTableIndices.InterfaceImpl] =
              this.interfaceImplArray;
          int classSize = this.tableColumnSizes[(int)MetaDataTableIndices.InterfaceImpl][0];
          int interfaceSize = this.tableColumnSizes[(int)MetaDataTableIndices.InterfaceImpl][1];
          for (int i = 0; i < count; i++) {
              int classIndex = ((classSize == 4) ?
                                reader.ReadInt32() :
                                reader.ReadUInt16());
              int interfaceIndex = ((interfaceSize == 4) ?
                                    reader.ReadInt32() :
                                    reader.ReadUInt16());
              this.interfaceImplArray[i] =
                  new MetaDataInterfaceImpl(classIndex, interfaceIndex);
          }
      }

      private void resolveInterfaceImplReferences() {
          int typeDefCount = this.typeDefArray.Length;
          ArrayList[] interfaceListArray = new ArrayList[typeDefCount+1];
          foreach (MetaDataInterfaceImpl interfaceImpl in
                   this.interfaceImplArray) {
              interfaceImpl.resolveReferences(this, interfaceListArray);
              // Console.WriteLine(interfaceImpl.ToStringLong());
          }
          for (int i = 1; i <= typeDefCount; i++) {
              MetaDataTypeDefinition classObject = this.getTypeDef(i);
              if (interfaceListArray[i] != null) {
                  MetaDataObject[] interfaceArray =
                      new MetaDataObject[interfaceListArray[i].Count];
                  interfaceListArray[i].CopyTo(interfaceArray);
                  classObject.resolveReferences(interfaceArray);
              }
              else {
                  classObject.resolveReferences(emptyInterfaceArray);
              }
          }
      }

      private void initializeMemberRefTable(BinaryReader reader) {
          int count = this.countArray[(int) MetaDataTableIndices.MemberRef];
          this.memberRefArray = new MetaDataMemberRef[count];
          this.metaDataTable[(int) MetaDataTableIndices.MemberRef] =
              this.memberRefArray;
          int classSize =
              this.tableColumnSizes[(int)MetaDataTableIndices.MemberRef][0];
          for (int i = 0; i < count; i++) {
              int classIndex = ((classSize == 4) ?
                                reader.ReadInt32() :
                                reader.ReadUInt16());
              int nameIndex = ((this.stringIndexSize == 4) ?
                               reader.ReadInt32() :
                               reader.ReadUInt16());
              String name = this.getString(nameIndex);
              int signatureIndex = ((this.blobIndexSize == 4) ?
                                    reader.ReadInt32() :
                                    reader.ReadUInt16());
              Signature signature = this.getSignature(signatureIndex);
              this.memberRefArray[i] =
                  new MetaDataMemberRef(classIndex, name, signature);
          }
      }

      private void resolveMemberRefReferences() {
          foreach (MetaDataMemberRef memberRef in this.memberRefArray) {
              memberRef.resolveReferences(this);
//                Console.WriteLine(memberRef.ToStringLong());
          }
      }

      private void initializeConstantTable(BinaryReader reader) {
          int count = this.countArray[(int) MetaDataTableIndices.Constant];
          this.constantArray = new MetaDataConstant[count];
          this.metaDataTable[(int) MetaDataTableIndices.Constant] =
              this.constantArray;
          int parentSize =
              this.tableColumnSizes[(int)MetaDataTableIndices.Constant][1];
          for (int i = 0; i < count; i++) {
              ElementTypes type = (ElementTypes) reader.ReadByte();
              byte padding = reader.ReadByte();
              int parentIndex = ((parentSize == 4) ?
                                 reader.ReadInt32() :
                                 reader.ReadUInt16());
              int valueIndex = ((this.blobIndexSize == 4) ?
                                reader.ReadInt32() :
                                reader.ReadUInt16());
              byte[] valueBuffer = this.getValueBuffer(valueIndex);
              this.constantArray[i] =
                  new MetaDataConstant(type, parentIndex, valueBuffer);
          }
      }

      private void resolveConstantReferences() {
          foreach (MetaDataConstant constant in this.constantArray) {
              constant.resolveReferences(this);
              MetaDataObject parent = constant.Parent;
              if (parent is MetaDataField) {
                  ((MetaDataField) parent).resolveReferences(constant);
              }
              else if (parent is MetaDataParam) {
                  ((MetaDataParam) parent).resolveReferences(constant);
              }
              else if (parent is MetaDataProperty) {
                  ((MetaDataProperty) parent).resolveReferences(constant);
              }
              else {
                  throw new IllegalMetaDataFormatException("Unexpected parent of constant: "+parent);
              }
              // Console.WriteLine(constant.ToStringLong());
          }
      }

      private void initializeCustomAttributeTable(BinaryReader reader) {
          int count =
              this.countArray[(int) MetaDataTableIndices.CustomAttribute];
          this.customAttributeArray = new MetaDataCustomAttribute[count];
          this.metaDataTable[(int) MetaDataTableIndices.CustomAttribute] =
              this.customAttributeArray;
          int parentSize = this.tableColumnSizes[(int)MetaDataTableIndices.CustomAttribute][0];
          int typeSize = this.tableColumnSizes[(int)MetaDataTableIndices.CustomAttribute][1];
          for (int i = 0; i < count; i++) {
              int parentIndex = ((parentSize == 4) ?
                                 reader.ReadInt32() :
                                 reader.ReadUInt16());
              int typeIndex = ((typeSize == 4) ?
                               reader.ReadInt32() :
                               reader.ReadUInt16());
              int valueIndex = ((this.blobIndexSize == 4) ?
                                reader.ReadInt32() :
                                reader.ReadUInt16());
              MetaDataObject type = this.getCustomAttributeType(typeIndex);
              byte[] valueBuffer = this.getBlobBytes(valueIndex);
              this.customAttributeArray[i] =
                  new MetaDataCustomAttribute(parentIndex, type, valueBuffer);
          }
      }

      private void resolveCustomAttributeReferences() {
          foreach (MetaDataCustomAttribute attribute in
                   this.customAttributeArray) {
              attribute.resolveReferences(this);
              // Console.WriteLine(attribute.ToStringLong());
          }
      }

      private void initializeFieldMarshalTable(BinaryReader reader) {
          int count = this.countArray[(int) MetaDataTableIndices.FieldMarshal];
          this.fieldMarshalArray = new MetaDataFieldMarshal[count];
          this.metaDataTable[(int) MetaDataTableIndices.FieldMarshal] =
              this.fieldMarshalArray;
          int parentSize =
              this.tableColumnSizes[(int)MetaDataTableIndices.FieldMarshal][0];
          for (int i = 0; i < count; i++) {
              int parentIndex = ((parentSize == 4) ?
                                 reader.ReadInt32() :
                                 reader.ReadUInt16());
              int nativeTypeIndex = ((this.blobIndexSize == 4) ?
                                     reader.ReadInt32() :
                                     reader.ReadUInt16());
              MarshalSpec nativeType = this.getNativeType(nativeTypeIndex);
              this.fieldMarshalArray[i] =
                  new MetaDataFieldMarshal(parentIndex, nativeType);
          }
      }

      private void resolveFieldMarshalReferences() {
          foreach (MetaDataFieldMarshal fieldMarshal in
                   this.fieldMarshalArray) {
              fieldMarshal.resolveReferences(this);
//                Console.WriteLine(fieldMarshal.ToStringLong());
          }
      }

      private void initializeDeclSecurityTable(BinaryReader reader) {
          int count = this.countArray[(int) MetaDataTableIndices.DeclSecurity];
          this.declSecurityArray = new MetaDataDeclSecurity[count];
          this.metaDataTable[(int) MetaDataTableIndices.DeclSecurity] =
              this.declSecurityArray;
          int parentSize = this.tableColumnSizes[(int) MetaDataTableIndices.DeclSecurity][1];
          for (int i = 0; i < count; i++) {
              short action = reader.ReadInt16();
              int parentIndex = ((parentSize == 4) ?
                                 reader.ReadInt32() :
                                 reader.ReadUInt16());
              int permissionSetIndex = ((this.blobIndexSize == 4) ?
                                        reader.ReadInt32() :
                                        reader.ReadUInt16());
              MetaDataBlob permissionSet =
                  this.getPermissionSet(permissionSetIndex);
              this.declSecurityArray[i] =
                  new MetaDataDeclSecurity(action, parentIndex, permissionSet);
          }
      }

      private void resolveDeclSecurityReferences() {
          foreach (MetaDataDeclSecurity declSecurity in
                   this.declSecurityArray) {
              declSecurity.resolveReferences(this);
//                Console.WriteLine(declSecurity.ToStringLong());
          }
      }

      private void initializeClassLayoutTable(BinaryReader reader) {
          int count = this.countArray[(int) MetaDataTableIndices.ClassLayout];
          this.classLayoutArray = new MetaDataClassLayout[count];
          this.metaDataTable[(int) MetaDataTableIndices.ClassLayout] =
              this.classLayoutArray;
          int parentSize =
              this.tableColumnSizes[(int) MetaDataTableIndices.ClassLayout][2];
          for (int i = 0; i < count; i++) {
              short packingSize = reader.ReadInt16();
              int classSize = reader.ReadInt32();
              int parentIndex = ((parentSize == 4) ?
                                 reader.ReadInt32() :
                                 reader.ReadUInt16());
              this.classLayoutArray[i] =
                  new MetaDataClassLayout(packingSize, classSize, parentIndex);
          }
      }

      private void resolveClassLayoutReferences() {
          foreach (MetaDataClassLayout classLayout in
                   this.classLayoutArray) {
              classLayout.resolveReferences(this);
//                Console.WriteLine(classLayout.ToStringLong());
          }
      }

      private void initializeFieldLayoutTable(BinaryReader reader) {
          int count = this.countArray[(int) MetaDataTableIndices.FieldLayout];
          this.fieldLayoutArray = new MetaDataFieldLayout[count];
          this.metaDataTable[(int) MetaDataTableIndices.FieldLayout] =
              this.fieldLayoutArray;
          int fieldSize =
              this.tableColumnSizes[(int) MetaDataTableIndices.FieldLayout][1];
          for (int i = 0; i < count; i++) {
              int offset = reader.ReadInt32();
              int fieldIndex = ((fieldSize == 4) ?
                                reader.ReadInt32() :
                                reader.ReadUInt16());
              MetaDataField field = this.getField(fieldIndex);
              MetaDataFieldLayout fieldLayout =
                  new MetaDataFieldLayout(offset, field);
              field.resolveReferences(fieldLayout);
              this.fieldLayoutArray[i] = fieldLayout;
          }
      }

      private void resolveFieldLayoutReferences() {
//            foreach (MetaDataFieldLayout fieldLayout in
//                     this.fieldLayoutArray) {
//                Console.WriteLine(fieldLayout.ToStringLong());
//            }
      }

      private void initializeStandAloneSigTable(BinaryReader reader) {
          int count =
              this.countArray[(int) MetaDataTableIndices.StandAloneSig];
          this.standAloneSigArray = new MetaDataStandAloneSig[count];
          this.metaDataTable[(int) MetaDataTableIndices.StandAloneSig] =
              this.standAloneSigArray;
          int signatureSize = this.tableColumnSizes[(int) MetaDataTableIndices.StandAloneSig][0];
          for (int i = 0; i < count; i++) {
              int signatureIndex = ((signatureSize == 4) ?
                                    reader.ReadInt32() :
                                    reader.ReadUInt16());
              Signature signature = this.getSignature(signatureIndex);
              this.standAloneSigArray[i] =
                  new MetaDataStandAloneSig(signature);
          }
      }

      private void resolveStandAloneSigReferences() {
          foreach (MetaDataStandAloneSig standAloneSig in
                   this.standAloneSigArray) {
              standAloneSig.resolveReferences(this);
//                Console.WriteLine(standAloneSig.ToStringLong());
           }
      }

      private void initializeEventMapTable(BinaryReader reader) {
          int count =
              this.countArray[(int) MetaDataTableIndices.EventMap];
          this.eventMapArray = new MetaDataEventMap[count];
          this.metaDataTable[(int) MetaDataTableIndices.EventMap] =
              this.eventMapArray;
          int parentSize =
              this.tableColumnSizes[(int) MetaDataTableIndices.EventMap][0];
          int eventListSize =
              this.tableColumnSizes[(int) MetaDataTableIndices.EventMap][1];
          for (int i = 0; i < count; i++) {
              int parentIndex = ((parentSize == 4) ?
                                 reader.ReadInt32() :
                                 reader.ReadUInt16());
              int eventListIndex = ((eventListSize == 4) ?
                                    reader.ReadInt32() :
                                    reader.ReadUInt16());
              this.eventMapArray[i] =
                  new MetaDataEventMap(parentIndex, eventListIndex);
          }
      }

      private void resolveEventMapReferences() {
          foreach (MetaDataEventMap eventMap in this.eventMapArray) {
              eventMap.resolveReferences(this);
//                Console.WriteLine(eventMap.ToStringLong());
          }
      }

      private void initializeEventPtrTable(BinaryReader reader) {
          int count =
              this.countArray[(int) MetaDataTableIndices.EventPtr];
          this.eventPtrArray = new MetaDataEventPtr[count];
          this.metaDataTable[(int) MetaDataTableIndices.EventPtr] =
              this.eventPtrArray;
          int eventSize =
              this.tableColumnSizes[(int) MetaDataTableIndices.EventPtr][0];
          for (int i = 0; i < count; i++) {
              int eventIndex = ((eventSize == 4) ?
                                reader.ReadInt32() :
                                reader.ReadUInt16());
              this.eventPtrArray[i] =
                  new MetaDataEventPtr(eventIndex);
          }
      }

      private void resolveEventPtrReferences() {
          foreach (MetaDataEventPtr eventPtr in this.eventPtrArray) {
              eventPtr.resolveReferences(this);
//                Console.WriteLine(eventPtr.ToStringLong());
          }
      }

      private void initializeEventTable(BinaryReader reader) {
          int count =
              this.countArray[(int) MetaDataTableIndices.Event];
          this.eventArray = new MetaDataEvent[count];
          this.metaDataTable[(int) MetaDataTableIndices.Event] =
              this.eventArray;
          int eventTypeSize =
              this.tableColumnSizes[(int) MetaDataTableIndices.Event][2];
          for (int i = 0; i < count; i++) {
              short eventFlags = reader.ReadInt16();
              int nameIndex = ((this.stringIndexSize == 4) ?
                               reader.ReadInt32() :
                               reader.ReadUInt16());
              String name = this.getString(nameIndex);
              int eventTypeIndex = ((eventTypeSize == 4) ?
                                    reader.ReadInt32() :
                                    reader.ReadUInt16());
              this.eventArray[i] =
                  new MetaDataEvent(eventFlags, name, eventTypeIndex);
          }
      }

      private void resolveEventReferences() {
          foreach (MetaDataEvent eventObject in this.eventArray) {
              eventObject.resolveReferences(this);
//                Console.WriteLine(eventObject.ToStringLong());
          }
      }

      private void initializePropertyMapTable(BinaryReader reader) {
          int count =
              this.countArray[(int) MetaDataTableIndices.PropertyMap];
          this.propertyMapArray = new MetaDataPropertyMap[count];
          this.metaDataTable[(int) MetaDataTableIndices.PropertyMap] =
              this.propertyMapArray;
          int parentSize =
              this.tableColumnSizes[(int) MetaDataTableIndices.PropertyMap][0];
          int propertyListSize =
              this.tableColumnSizes[(int) MetaDataTableIndices.PropertyMap][1];
          for (int i = 0; i < count; i++) {
              int parentIndex = ((parentSize == 4) ?
                                 reader.ReadInt32() :
                                 reader.ReadUInt16());
              int propertyListIndex = ((propertyListSize == 4) ?
                                       reader.ReadInt32() :
                                       reader.ReadUInt16());
              this.propertyMapArray[i] =
                  new MetaDataPropertyMap(parentIndex, propertyListIndex);
          }
      }

      private void resolvePropertyMapReferences() {
          foreach (MetaDataPropertyMap propertyMap in this.propertyMapArray) {
              propertyMap.resolveReferences(this);
//                Console.WriteLine(propertyMap.ToStringLong());
          }
      }

      private void initializePropertyPtrTable(BinaryReader reader) {
          int count =
              this.countArray[(int) MetaDataTableIndices.PropertyPtr];
          this.propertyPtrArray = new MetaDataPropertyPtr[count];
          this.metaDataTable[(int) MetaDataTableIndices.PropertyPtr] =
              this.propertyPtrArray;
          int propertySize =
              this.tableColumnSizes[(int) MetaDataTableIndices.PropertyPtr][0];
          for (int i = 0; i < count; i++) {
              int propertyIndex = ((propertySize == 4) ?
                                   reader.ReadInt32() :
                                   reader.ReadUInt16());
              this.propertyPtrArray[i] =
                  new MetaDataPropertyPtr(propertyIndex);
          }
      }

      private void resolvePropertyPtrReferences() {
          foreach (MetaDataPropertyPtr propertyPtr in this.propertyPtrArray) {
              propertyPtr.resolveReferences(this);
//                Console.WriteLine(propertyPtr.ToStringLong());
          }
      }

      private void initializePropertyTable(BinaryReader reader) {
          int count =
              this.countArray[(int) MetaDataTableIndices.Property];
          this.propertyArray = new MetaDataProperty[count];
          this.metaDataTable[(int) MetaDataTableIndices.Property] =
              this.propertyArray;
          for (int i = 0; i < count; i++) {
              short flags = reader.ReadInt16();
              int nameIndex = ((this.stringIndexSize == 4) ?
                               reader.ReadInt32() :
                               reader.ReadUInt16());
              String name = this.getString(nameIndex);
              int typeIndex = ((this.blobIndexSize == 4) ?
                               reader.ReadInt32() :
                               reader.ReadUInt16());
              Signature type = this.getSignature(typeIndex);
              this.propertyArray[i] =
                  new MetaDataProperty(flags, name, type);
          }
      }

      private void resolvePropertyReferences() {
          foreach (MetaDataProperty property in this.propertyArray) {
              property.resolveReferences(this);
//                Console.WriteLine(property.ToStringLong());
          }
      }

      private void initializeMethodSemanticsTable(BinaryReader reader) {
          int count =
              this.countArray[(int) MetaDataTableIndices.MethodSemantics];
          this.methodSemanticsArray = new MetaDataMethodSemantics[count];
          this.metaDataTable[(int) MetaDataTableIndices.MethodSemantics] =
              this.methodSemanticsArray;
          int methodSize = this.tableColumnSizes[(int) MetaDataTableIndices.MethodSemantics][1];
          int associationSize = this.tableColumnSizes[(int) MetaDataTableIndices.MethodSemantics][2];
          for (int i = 0; i < count; i++) {
              short semantic = reader.ReadInt16();
              int methodIndex = ((methodSize == 4) ?
                                 reader.ReadInt32() :
                                 reader.ReadUInt16());
              int associationIndex = ((associationSize == 4) ?
                                      reader.ReadInt32() :
                                      reader.ReadUInt16());
              this.methodSemanticsArray[i] =
                  new MetaDataMethodSemantics(semantic, methodIndex,
                                              associationIndex);
          }
      }

      private void resolveMethodSemanticsReferences() {
          foreach (MetaDataMethodSemantics methodSemantics in
                   this.methodSemanticsArray) {
              methodSemantics.resolveReferences(this);
//                Console.WriteLine(methodSemantics.ToStringLong());
          }
      }

      private void initializeMethodImplTable(BinaryReader reader) {
          int count =
              this.countArray[(int) MetaDataTableIndices.MethodImpl];
          this.methodImplArray = new MetaDataMethodImpl[count];
          this.metaDataTable[(int) MetaDataTableIndices.MethodImpl] =
              this.methodImplArray;
          int classSize =
              this.tableColumnSizes[(int) MetaDataTableIndices.MethodImpl][0];
          int bodySize =
              this.tableColumnSizes[(int) MetaDataTableIndices.MethodImpl][1];
          int declarationSize =
              this.tableColumnSizes[(int) MetaDataTableIndices.MethodImpl][2];
          for (int i = 0; i < count; i++) {
              int classIndex = ((classSize == 4) ?
                                reader.ReadInt32() :
                                reader.ReadUInt16());
              int bodyIndex = ((bodySize == 4) ?
                               reader.ReadInt32() :
                               reader.ReadUInt16());
              int declarationIndex = ((declarationSize == 4) ?
                                      reader.ReadInt32() :
                                      reader.ReadUInt16());
              this.methodImplArray[i] =
                  new MetaDataMethodImpl(classIndex, bodyIndex,
                                         declarationIndex);
          }
      }

      private void resolveMethodImplReferences() {
          foreach (MetaDataMethodImpl methodImpl in this.methodImplArray) {
              methodImpl.resolveReferences(this);
//                Console.WriteLine(methodImpl.ToStringLong());
          }
      }

      private void initializeModuleRefTable(BinaryReader reader) {
          int count =
              this.countArray[(int) MetaDataTableIndices.ModuleRef];
          this.moduleRefArray = new MetaDataModuleRef[count];
          this.metaDataTable[(int) MetaDataTableIndices.ModuleRef] =
              this.moduleRefArray;
          for (int i = 0; i < count; i++) {
              int nameIndex = ((this.stringIndexSize == 4) ?
                               reader.ReadInt32() :
                               reader.ReadUInt16());
              String name = this.getString(nameIndex);
              this.moduleRefArray[i] =
                  new MetaDataModuleRef(name);
          }
      }

      private void resolveModuleRefReferences() {
//            foreach (MetaDataModuleRef moduleRef in this.moduleRefArray) {
//                Console.WriteLine(moduleRef.ToStringLong());
//            }
      }

      private void initializeTypeSpecTable(BinaryReader reader) {
          int count =
              this.countArray[(int) MetaDataTableIndices.TypeSpec];
          this.typeSpecArray = new MetaDataTypeSpec[count];
          this.metaDataTable[(int) MetaDataTableIndices.TypeSpec] =
              this.typeSpecArray;
          for (int i = 0; i < count; i++) {
              int signatureIndex = ((this.blobIndexSize == 4) ?
                                    reader.ReadInt32() :
                                    reader.ReadUInt16());
              Signature signature = this.getSignature(signatureIndex);
              this.typeSpecArray[i] = new MetaDataTypeSpec(signature);
          }
      }

      private void resolveTypeSpecReferences() {
          foreach (MetaDataTypeSpec typeSpec in this.typeSpecArray) {
              typeSpec.resolveReferences(this);
//                Console.WriteLine(typeSpec.ToStringLong());
          }
      }

      private void initializeImplMapTable(BinaryReader reader) {
          int count =
              this.countArray[(int) MetaDataTableIndices.ImplMap];
          this.implMapArray = new MetaDataImplMap[count];
          this.metaDataTable[(int) MetaDataTableIndices.ImplMap] =
              this.implMapArray;
          int memberForwardedSize =
              this.tableColumnSizes[(int) MetaDataTableIndices.ImplMap][1];
          int importScopeSize =
              this.tableColumnSizes[(int) MetaDataTableIndices.ImplMap][3];
          for (int i = 0; i < count; i++) {
              short flags = reader.ReadInt16();
              int memberForwardedIndex = ((memberForwardedSize == 4) ?
                                          reader.ReadInt32() :
                                          reader.ReadUInt16());
              int importNameIndex = ((this.stringIndexSize == 4) ?
                                     reader.ReadInt32() :
                                     reader.ReadUInt16());
              String importName = this.getString(importNameIndex);
              int importScopeIndex = ((importScopeSize == 4) ?
                                      reader.ReadInt32() :
                                      reader.ReadUInt16());
              this.implMapArray[i] =
                  new MetaDataImplMap(flags, memberForwardedIndex,
                                      importName, importScopeIndex);
          }
      }

      private void resolveImplMapReferences() {
          foreach (MetaDataImplMap implMap in this.implMapArray) {
              implMap.resolveReferences(this);
//                Console.WriteLine(implMap.ToStringLong());
          }
      }

      private void initializeFieldRVATable(BinaryReader reader) {
          int count =
              this.countArray[(int) MetaDataTableIndices.FieldRVA];
          this.fieldRVAArray = new MetaDataFieldRVA[count];
          this.metaDataTable[(int) MetaDataTableIndices.FieldRVA] =
              this.fieldRVAArray;
          int fieldSize =
              this.tableColumnSizes[(int) MetaDataTableIndices.FieldRVA][1];
          for (int i = 0; i < count; i++) {
              int rva = reader.ReadInt32();
              int fieldIndex = ((fieldSize == 4) ?
                                reader.ReadInt32() :
                                reader.ReadUInt16());
              MetaDataField field = this.getField(fieldIndex);
              this.fieldRVAArray[i] = new MetaDataFieldRVA(rva, field);
          }
      }

      private void resolveFieldRVAReferences() {
          foreach (MetaDataFieldRVA fieldRVA in this.fieldRVAArray) {
              // Console.WriteLine(fieldRVA.ToStringLong());
              // Console.WriteLine(fieldRVA.Field.ToStringLong());
              fieldRVA.resolveReferences(this, this.peLoader, this.fileStream);
              // Console.WriteLine(fieldRVA.ToStringLong());
          }
      }

      private void initializeENCLogTable(BinaryReader reader) {
          int count =
              this.countArray[(int) MetaDataTableIndices.ENCLog];
          if (count != 0) {
              throw new IllegalMetaDataFormatException("Found ENCLog entries");
          }
      }

      private void resolveENCLogReferences() {
          // Do nothing
      }

      private void initializeENCMapTable(BinaryReader reader) {
          int count =
              this.countArray[(int) MetaDataTableIndices.ENCMap];
          if (count != 0) {
              throw new IllegalMetaDataFormatException("Found ENCMap entries");
          }
      }

      private void resolveENCMapReferences() {
          // Do nothing
      }

      private void initializeAssemblyTable(BinaryReader reader) {
          int count =
              this.countArray[(int) MetaDataTableIndices.Assembly];
          this.assemblyArray = new MetaDataAssembly[count];
          this.metaDataTable[(int) MetaDataTableIndices.Assembly] =
              this.assemblyArray;
          for (int i = 0; i < count; i++) {
              int hashAlgorithmId = reader.ReadInt32();
              short majorVersion = reader.ReadInt16();
              short minorVersion = reader.ReadInt16();
              short buildNumber = reader.ReadInt16();
              short revisionNumber = reader.ReadInt16();
              int flags = reader.ReadInt32();
              int publicKeyIndex = ((this.blobIndexSize == 4) ?
                                    reader.ReadInt32() :
                                    reader.ReadUInt16());
              byte[] publicKey = this.getPublicKey(publicKeyIndex);
              int nameIndex, localeIndex;
              if (this.stringIndexSize == 4) {
                  nameIndex = reader.ReadInt32();
                  localeIndex = reader.ReadInt32();
              }
              else {
                  nameIndex = reader.ReadUInt16();
                  localeIndex = reader.ReadUInt16();
              }
              String name = this.getString(nameIndex);
              String locale = this.getString(localeIndex);
              this.assemblyArray[i] =
                  new MetaDataAssembly(hashAlgorithmId,
                                       majorVersion, minorVersion,
                                       buildNumber, revisionNumber,
                                       flags, publicKey, name, locale);
          }
      }

      private void resolveAssemblyReferences() {
//            foreach (MetaDataAssembly assembly in this.assemblyArray) {
//                Console.WriteLine(assembly.ToStringLong());
//            }
      }

      private void initializeAssemblyProcessorTable(BinaryReader reader) {
          int count =
              this.countArray[(int) MetaDataTableIndices.AssemblyProcessor];
          this.assemblyProcessorArray = new MetaDataAssemblyProcessor[count];
          this.metaDataTable[(int) MetaDataTableIndices.AssemblyProcessor] =
              this.assemblyProcessorArray;
          for (int i = 0; i < count; i++) {
              int processor = reader.ReadInt32();
              this.assemblyProcessorArray[i] =
                  new MetaDataAssemblyProcessor(processor);
          }
      }

      private void resolveAssemblyProcessorReferences() {
//            foreach (MetaDataAssemblyProcessor assemblyProcessor in
//                     this.assemblyProcessorArray) {
//                Console.WriteLine(assemblyProcessor.ToStringLong());
//            }
      }

      private void initializeAssemblyOSTable(BinaryReader reader) {
          int count =
              this.countArray[(int) MetaDataTableIndices.AssemblyOS];
          this.assemblyOSArray = new MetaDataAssemblyOS[count];
          this.metaDataTable[(int) MetaDataTableIndices.AssemblyOS] =
              this.assemblyOSArray;
          for (int i = 0; i < count; i++) {
              int platformID = reader.ReadInt32();
              int majorVersion = reader.ReadInt32();
              int minorVersion = reader.ReadInt32();
              this.assemblyOSArray[i] =
                  new MetaDataAssemblyOS(platformID, majorVersion,
                                         minorVersion);
          }
      }

      private void resolveAssemblyOSReferences() {
//            foreach (MetaDataAssemblyOS assemblyOS in
//                     this.assemblyOSArray) {
//                Console.WriteLine(assemblyOS.ToStringLong());
//            }
      }

      private void initializeAssemblyRefTable(BinaryReader reader) {
          int count =
              this.countArray[(int) MetaDataTableIndices.AssemblyRef];
          this.assemblyRefArray = new MetaDataAssemblyRef[count];
          this.metaDataTable[(int) MetaDataTableIndices.AssemblyRef] =
              this.assemblyRefArray;
          for (int i = 0; i < count; i++) {
              short majorVersion = reader.ReadInt16();
              short minorVersion = reader.ReadInt16();
              short buildNumber = reader.ReadInt16();
              short revisionNumber = reader.ReadInt16();
              int flags = reader.ReadInt32();
              int publicKeyIndex = ((this.blobIndexSize == 4) ?
                                    reader.ReadInt32() :
                                    reader.ReadUInt16());
              byte[] publicKey = this.getPublicKey(publicKeyIndex);
              int nameIndex, localeIndex;
              if (this.stringIndexSize == 4) {
                  nameIndex = reader.ReadInt32();
                  localeIndex = reader.ReadInt32();
              }
              else {
                   nameIndex = reader.ReadUInt16();
                   localeIndex = reader.ReadUInt16();
              }
              String name = this.getString(nameIndex);
              String locale = this.getString(localeIndex);
              int hashValueIndex = ((this.blobIndexSize == 4) ?
                                    reader.ReadInt32() :
                                    reader.ReadUInt16());
              byte[] hashValue = this.getHashValue(hashValueIndex);
              this.assemblyRefArray[i] =
                  new MetaDataAssemblyRef(majorVersion, minorVersion,
                                          buildNumber, revisionNumber,
                                          flags, publicKey, name, locale,
                                          hashValue);
          }
      }

      private void resolveAssemblyRefReferences() {
//            foreach (MetaDataAssemblyRef assemblyRef in
//                     this.assemblyRefArray) {
//                Console.WriteLine(assemblyRef.ToStringLong());
//            }
      }

      private void initializeAssemblyRefProcessorTable(BinaryReader reader) {
          int count =
              this.countArray[(int) MetaDataTableIndices.AssemblyRefProcessor];
          this.assemblyRefProcessorArray =
              new MetaDataAssemblyRefProcessor[count];
          this.metaDataTable[(int) MetaDataTableIndices.AssemblyRefProcessor] =
              this.assemblyRefProcessorArray;
          int assemblyRefSize = this.tableColumnSizes[(int) MetaDataTableIndices.AssemblyRefProcessor][1];
          for (int i = 0; i < count; i++) {
              int processor = reader.ReadInt32();
              int assemblyRefIndex = ((assemblyRefSize == 4) ?
                                      reader.ReadInt32() :
                                      reader.ReadUInt16());
              MetaDataAssemblyRef assemblyRef =
                  this.getAssemblyRef(assemblyRefIndex);
              this.assemblyRefProcessorArray[i] =
                  new MetaDataAssemblyRefProcessor(processor, assemblyRef);
          }
      }

      private void resolveAssemblyRefProcessorReferences() {
//            foreach (MetaDataAssemblyRefProcessor assemblyRefProcessor in
//                     this.assemblyRefProcessorArray) {
//                Console.WriteLine(assemblyRefProcessor.ToStringLong());
//            }
      }

      private void initializeAssemblyRefOSTable(BinaryReader reader) {
          int count =
              this.countArray[(int) MetaDataTableIndices.AssemblyRefOS];
          this.assemblyRefOSArray = new MetaDataAssemblyRefOS[count];
          this.metaDataTable[(int) MetaDataTableIndices.AssemblyRefOS] =
              this.assemblyRefOSArray;
          int assemblyRefSize = this.tableColumnSizes[(int) MetaDataTableIndices.AssemblyRefOS][3];
          for (int i = 0; i < count; i++) {
              int platformID = reader.ReadInt32();
              int majorVersion = reader.ReadInt32();
              int minorVersion = reader.ReadInt32();
              int assemblyRefIndex = ((assemblyRefSize == 4) ?
                                      reader.ReadInt32() :
                                      reader.ReadUInt16());
              MetaDataAssemblyRef assemblyRef =
                  this.getAssemblyRef(assemblyRefIndex);
              this.assemblyRefOSArray[i] =
                  new MetaDataAssemblyRefOS(platformID, majorVersion,
                                            minorVersion, assemblyRef);
          }
      }

      private void resolveAssemblyRefOSReferences() {
//            foreach (MetaDataAssemblyRefOS assemblyRefOS in
//                     this.assemblyRefOSArray) {
//                Console.WriteLine(assemblyRefOS.ToStringLong());
//            }
      }

      private void initializeFileTable(BinaryReader reader) {
          int count =
              this.countArray[(int) MetaDataTableIndices.File];
          this.fileArray = new MetaDataFile[count];
          this.metaDataTable[(int) MetaDataTableIndices.File] =
              this.fileArray;
          for (int i = 0; i < count; i++) {
              int flags = reader.ReadInt32();
              int nameIndex = ((this.stringIndexSize == 4) ?
                               reader.ReadInt32() :
                               reader.ReadUInt16());
              String name = this.getString(nameIndex);
              int hashValueIndex = ((this.blobIndexSize == 4) ?
                                    reader.ReadInt32() :
                                    reader.ReadUInt16());
              byte[] hashValue = this.getHashValue(hashValueIndex);
              this.fileArray[i] = new MetaDataFile(flags, name, hashValue);
          }
      }

      private void resolveFileReferences() {
//            foreach (MetaDataFile file in this.fileArray) {
//                Console.WriteLine(file.ToStringLong());
//            }
      }

      private void initializeExportedTypeTable(BinaryReader reader) {
          int count =
              this.countArray[(int) MetaDataTableIndices.ExportedType];
          this.exportedTypeArray = new MetaDataExportedType[count];
          this.metaDataTable[(int) MetaDataTableIndices.ExportedType] =
              this.exportedTypeArray;
          int implementationSize = this.tableColumnSizes[(int) MetaDataTableIndices.ExportedType][4];
          for (int i = 0; i < count; i++) {
              int flags = reader.ReadInt32();
              int typeDefId = reader.ReadInt32();
              int typeNameIndex, typeNamespaceIndex;
              if (this.stringIndexSize == 4) {
                  typeNameIndex = reader.ReadInt32();
                  typeNamespaceIndex = reader.ReadInt32();
              }
              else {
                  typeNameIndex = reader.ReadUInt16();
                  typeNamespaceIndex = reader.ReadUInt16();
              }
              String typeName = this.getString(typeNameIndex);
              String typeNamespace = this.getString(typeNamespaceIndex);
              int implementationIndex = ((implementationSize == 4) ?
                                         reader.ReadInt32() :
                                         reader.ReadUInt16());
              this.exportedTypeArray[i] =
                  new MetaDataExportedType(flags, typeDefId, typeName,
                                           typeNamespace, implementationIndex);
          }
      }

      private void resolveExportedTypeReferences() {
          foreach (MetaDataExportedType exportedType in
                   this.exportedTypeArray) {
              exportedType.resolveReferences(this);
//                Console.WriteLine(exportedType.ToStringLong());
          }
      }

      private void initializeManifestResourceTable(BinaryReader reader) {
          int count =
              this.countArray[(int) MetaDataTableIndices.ManifestResource];
          this.manifestResourceArray = new MetaDataManifestResource[count];
          this.metaDataTable[(int) MetaDataTableIndices.ManifestResource] =
              this.manifestResourceArray;
          int implementationSize = this.tableColumnSizes[(int) MetaDataTableIndices.ManifestResource][3];
          for (int i = 0; i < count; i++) {
              int offset = reader.ReadInt32();
              int flags = reader.ReadInt32();
              int nameIndex = ((this.stringIndexSize == 4) ?
                               reader.ReadInt32() :
                               reader.ReadUInt16());
              String name = this.getString(nameIndex);
              int implementationIndex = ((implementationSize == 4) ?
                                         reader.ReadInt32() :
                                         reader.ReadUInt16());
              byte[] data = ((implementationIndex == 0) ?
                             this.getResourceBytes(offset) :
                             null);
              // Embedded resource
              this.manifestResourceArray[i] =
                  new MetaDataManifestResource(offset, flags, name, data,
                                               implementationIndex);
          }
      }

      private void resolveManifestResourceReferences() {
          foreach (MetaDataManifestResource manifestResource in
                   this.manifestResourceArray) {
              manifestResource.resolveReferences(this);
//                Console.WriteLine(manifestResource.ToStringLong());
          }
      }

      private void initializeNestedClassTable(BinaryReader reader) {
          int count =
              this.countArray[(int) MetaDataTableIndices.NestedClass];
          this.nestedClassArray = new MetaDataNestedClass[count];
          this.metaDataTable[(int) MetaDataTableIndices.NestedClass] =
              this.nestedClassArray;
          int nestedClassSize =
              this.tableColumnSizes[(int) MetaDataTableIndices.NestedClass][0];
          int enclosingClassSize =
              this.tableColumnSizes[(int) MetaDataTableIndices.NestedClass][1];
          int typeDefCount = this.typeDefArray.Length;;
          ArrayList[] nestedClassListArray = new ArrayList[typeDefCount+1];
          for (int i = 0; i < count; i++) {
              int nestedClassIndex = ((nestedClassSize == 4) ?
                                      reader.ReadInt32() :
                                      reader.ReadUInt16());
              int enclosingClassIndex = ((enclosingClassSize == 4) ?
                                         reader.ReadInt32() :
                                         reader.ReadUInt16());
              MetaDataTypeDefinition nestedClass =
                  this.getTypeDef(nestedClassIndex);
              MetaDataTypeDefinition enclosingClass =
                  this.getTypeDef(enclosingClassIndex);
              ArrayList nestedClassList =
                  nestedClassListArray[enclosingClassIndex];
              if (nestedClassList == null) {
                  nestedClassList = new ArrayList(2);
                  nestedClassListArray[enclosingClassIndex] = nestedClassList;
              }
              nestedClassList.Add(nestedClass);
              nestedClass.resolveReferences(enclosingClass);
              this.nestedClassArray[i] =
                  new MetaDataNestedClass(nestedClass, enclosingClass);
          }
          for (int i = 1; i <= typeDefCount; i++) {
              ArrayList nestedClassList = nestedClassListArray[i];
              MetaDataTypeDefinition[] nestedClasses;
              if (nestedClassList != null) {
                  int nestedCount = nestedClassList.Count;
                  nestedClasses = new MetaDataTypeDefinition[nestedCount];
                  for (int j = 0; j < nestedCount; j++) {
                      nestedClasses[j] = (MetaDataTypeDefinition)
                          nestedClassList[j];
                  }
              }
              else {
                  nestedClasses = emptyNestedClassArray;
              }
              this.getTypeDef(i).resolveReferences(nestedClasses);
          }
      }

      private void resolveNestedClassReferences() {
//            foreach (MetaDataNestedClass nestedClass in
//                     this.nestedClassArray) {
//                Console.WriteLine(nestedClass.ToStringLong());
//            }
      }

      private void initializeGenericParamTable(BinaryReader reader) {
          int count =
              this.countArray[(int) MetaDataTableIndices.GenericParam];
          //System.Console.WriteLine("Found " + count + " GenericParam entries");

          this.genericParamArray = new MetaDataGenericParam[count];
          this.metaDataTable[(int) MetaDataTableIndices.GenericParam] =
              this.genericParamArray;

          int ownerSize =
              this.tableColumnSizes[(int) MetaDataTableIndices.GenericParam][2];
          int kindSize =
              this.tableColumnSizes[(int) MetaDataTableIndices.GenericParam][4];

          for (int i = 0; i < count; i++) {
              short number = reader.ReadInt16();
              short flags = reader.ReadInt16();
              int ownerIndex = ((ownerSize == 4) ?
                                reader.ReadInt32() :
                                reader.ReadUInt16());
              int nameIndex = ((this.stringIndexSize == 4) ?
                               reader.ReadInt32() :
                               reader.ReadUInt16());
              String name = this.getString(nameIndex);
              int kind = ((kindSize == 4) ?
                          reader.ReadInt32() :
                          reader.ReadUInt16());

              this.genericParamArray[i] =
                  new MetaDataGenericParam(number, flags, ownerIndex,
                                           name, kind);
          }
      }

      private void resolveGenericParamReferences() {
          foreach (MetaDataGenericParam genericParam in
                   this.genericParamArray) {
              genericParam.resolveReferences(this);
          }
      }

      private void initializeMethodSpecTable(BinaryReader reader) {
          int count =
              this.countArray[(int) MetaDataTableIndices.MethodSpec];
          //System.Console.WriteLine("Found " + count + " MethodSpec entries");

          this.methodSpecArray = new MetaDataMethodSpec[count];
          this.metaDataTable[(int) MetaDataTableIndices.MethodSpec] =
              this.methodSpecArray;

          int methodSize =
              this.tableColumnSizes[(int) MetaDataTableIndices.MethodSpec][0];

          for (int i = 0; i < count; i++) {
              int methodIndex = ((methodSize == 4) ?
                                 reader.ReadInt32() :
                                 reader.ReadUInt16());

              int instantiationIndex = ((this.blobIndexSize == 4) ?
                                        reader.ReadInt32() :
                                        reader.ReadUInt16());
              byte[] instantiationValue = this.getHashValue(instantiationIndex);

              this.methodSpecArray[i] =
                  new MetaDataMethodSpec(methodIndex, instantiationValue);
          }
      }

      private void resolveMethodSpecReferences() {
          foreach (MetaDataMethodSpec methodSpec in
                   this.methodSpecArray) {
              methodSpec.resolveReferences(this);
              // Console.WriteLine(methodSpec.ToStringLong());
          }
      }

      private void initializeGenericParamConstraintTable(BinaryReader reader) {
          int count =
              this.countArray[(int)
                              MetaDataTableIndices.GenericParamConstraint];
          //System.Console.WriteLine("Found " + count
          //                         + " GenericParamConstraint entries");

          this.genericParamConstraintArray =
              new MetaDataGenericParamConstraint[count];
          this.metaDataTable[(int) MetaDataTableIndices.GenericParamConstraint]
              = this.genericParamConstraintArray;

          int ownerSize = this.tableColumnSizes
              [(int) MetaDataTableIndices.GenericParamConstraint][0];
          int constraintSize = this.tableColumnSizes
              [(int) MetaDataTableIndices.GenericParamConstraint][1];

          for (int i = 0; i < count; i++) {
              int ownerIndex = ((ownerSize == 4) ?
                                reader.ReadInt32() :
                                reader.ReadUInt16());
              int constraintIndex = ((constraintSize == 4) ?
                                     reader.ReadInt32() :
                                     reader.ReadUInt16());

              this.genericParamConstraintArray[i] =
                  new MetaDataGenericParamConstraint(ownerIndex,
                                                     constraintIndex);
          }
      }

      private void resolveGenericParamConstraintReferences() {
          foreach (MetaDataGenericParamConstraint constraint in
                   this.genericParamConstraintArray) {
              constraint.resolveReferences(this);
          }
      }

      private void initializeRelocationTable() {
          // read in relocation tables
          int relocationOffset = peLoader.getRelocationOffset();
          ArrayList relocations = new ArrayList();
          if (relocationOffset > 0) {
              System.Console.WriteLine("Has relocation table");
              // has relocation table
              fileStream.Seek(relocationOffset, SeekOrigin.Begin);
              BinaryReader relocReader = new BinaryReader(fileStream);
              int rva = relocReader.ReadInt32();
              while (rva > 0) {
                  int size = relocReader.ReadInt32();
                  for (int i = 8; i < size; i += 2) {
                      int relocRVA = relocReader.ReadInt16();
                      if (relocRVA != 0) {
                          if ((relocRVA & 0x3000) != 0x3000)
                              System.Console.WriteLine("Warnging: unknown relocation type");
                          relocRVA &= 0x0FFF;    // the first 4 bits are types
                          relocRVA += rva;
                          relocations.Add(relocRVA);
                      }
                  }
                  rva = relocReader.ReadInt32();
              }
          }
          else {
              System.Console.WriteLine("Has no relocation table");
          }
          relocationArray = relocations.ToArray();

      }

      public bool RVAHasRelocation(int rva) {
          Object[] relocations = this.relocationArray;
          for (int i = 0; i < relocations.Length; i++) {
              if (rva == (int) relocations[i]) {
                  return true;
              }
          }
          return false;
      }

      private void initializeVtableFixupTable() {
          // Read the vtableFixup data, if there is any
          int vtableFixupOffset = peLoader.getVtableFixupOffset();
          int vtableFixupSize = peLoader.getVtableFixupSize();
          if (vtableFixupOffset > 0 && vtableFixupSize > 0) {
              fileStream.Seek(vtableFixupOffset, SeekOrigin.Begin);
              BinaryReader vtableReader = new BinaryReader(fileStream);
              if (vtableFixupSize % 8 != 0) {
                  System.Console.WriteLine("Warning: fixup size is not multiple of 8 bytes !!");
              }

              // each entry is 8 bytes, first 4 bytes is RVA,
              // followed by 2 bytes of count, 2 bytes of type
              int fixupCount = vtableFixupSize / 8;
              int[] rva = new int[fixupCount];
              short[] size = new short[fixupCount];
              short[] type = new short[fixupCount];
              for (int i = 0; i < fixupCount; i++) {
                  rva[i] = vtableReader.ReadInt32();
                  size[i] = vtableReader.ReadInt16();
                  type[i] = vtableReader.ReadInt16();
              }

              this.vtableFixupArray = new MetaDataVtableFixup[fixupCount];
              for (int i = 0; i < fixupCount; i++) {
                  int currRVA = rva[i];
                  short currSize = size[i];
                  COR_VTABLE currType = (COR_VTABLE) type[i];
                  // read in the fixup token
                  int offset = peLoader.VaToOffset(currRVA);
                  fileStream.Seek(offset, SeekOrigin.Begin);
                  BinaryReader tokenReader = new BinaryReader(fileStream);
                  MetaDataMethod[] fixupMethods = new MetaDataMethod[currSize];
                  for (int index = 0; index < currSize; index++) {
                      int token = tokenReader.ReadInt32();
                      fixupMethods[index] =
                          (MetaDataMethod)this.getObjectFromToken(token);
                  }
                  this.vtableFixupArray[i] =
                      new MetaDataVtableFixup(currRVA, currSize, currType,
                                              fixupMethods);
              }
          }
      }

      public bool HasVtableFixup() {
          return (this.vtableFixupArray != null);
      }

      private void initializeDelayIATTable() {
          // Read in the dalay IAT table, if there is any
          int delayIATOffset = peLoader.getDelayIATOffset();
          int delayIATSize = peLoader.getDelayIATSize();
          if (delayIATOffset > 0 && delayIATSize > 0) {
              fileStream.Seek(delayIATOffset, SeekOrigin.Begin);
              BinaryReader delayIATReader = new BinaryReader(fileStream);
              int characteristics = delayIATReader.ReadInt32();
              int addressOfDllName =
                  peLoader.VaToOffset(delayIATReader.ReadInt32());
              int addressOfHModule = delayIATReader.ReadInt32();
              int rvaOfIAT = peLoader.VaToOffset(delayIATReader.ReadInt32());
              int nameTable = peLoader.VaToOffset(delayIATReader.ReadInt32());

              // read in dll name
              string dllName = peLoader.readString(addressOfDllName);

              // read in import address table
              fileStream.Seek(rvaOfIAT, SeekOrigin.Begin);
              BinaryReader IATReader = new BinaryReader(fileStream);
              int importAddress = IATReader.ReadInt32();
              int count = 0;
              ArrayList imports = new ArrayList();
              while (importAddress != 0) {
                  count++;
                  imports.Add(importAddress);
                  importAddress = IATReader.ReadInt32();
              }
              object[] importArray = imports.ToArray();

              // read in the names
              fileStream.Seek(nameTable, SeekOrigin.Begin);
              BinaryReader nameAddrReader = new BinaryReader(fileStream);
              int[] nameAddress = new int[count];
              for (int i = 0; i < count; i++) {
                  int nameAddr = nameAddrReader.ReadInt32();
                  nameAddress[i] = peLoader.VaToOffset(nameAddr + 2);
              }

              String[] names = new String[count];
              for (int i = 0; i < count; i++) {
                  names[i] = peLoader.readString(nameAddress[i]);
              }

              this.delayImportTable =
                  new MetaDataDelayImportTable(dllName, importArray,
                                               names);

              System.Console.WriteLine(this.delayImportTable.ToString());
          }
      }

      // State

      private readonly PELoader      peLoader;
      private readonly Stream    fileStream;
      private   readonly int           metaDataOffset;
      private   readonly StorageStream dataStream;
      private   readonly StorageStream stringPoolStream;
      private   readonly StorageStream userBlobPoolStream;
      private   readonly StorageStream guidPoolStream;
      private   readonly StorageStream blobPoolStream;
      // Schema fields (for logical tables)
      private int           reserved;
      private byte          majorVersion;
      private byte          minorVersion;
      private byte          heapBits;
      private byte          rowId;
      private long          maskValid;
      private long          maskSorted;
      private int[]         countArray = new int[(int) MetaDataTableIndices.Count];
      private byte[][]      tableColumnSizes = new byte[(int) MetaDataTableIndices.Count][];
      private byte[][]      tableColumnOffsets = new byte[(int) MetaDataTableIndices.Count][];
      private byte[]        tableRowSizes = new byte[(int) MetaDataTableIndices.Count];
      private int           extraData;
      private byte          stringIndexSize;
      private byte          guidIndexSize;
      private byte          blobIndexSize;

      private readonly byte[]        stringStreamBuffer;
      private readonly byte[]        blobStreamBuffer;
      private readonly byte[]        userStringStreamBuffer;
      private readonly byte[]        resourceBuffer;
      private readonly Guid[]        guidArray;

      private MetaDataObject[][] metaDataTable;
      private MetaDataModule[] moduleArray;
      private MetaDataTypeReference[] typeRefArray;
      private MetaDataTypeDefinition[] typeDefArray;
      private MetaDataFieldPtr[] fieldPtrArray;
      private MetaDataField[] fieldArray;
      private MetaDataMethodPtr[] methodPtrArray;
      private MetaDataMethod[] methodArray;
      private MetaDataParamPtr[] paramPtrArray;
      private MetaDataParam[] paramArray;
      private MetaDataInterfaceImpl[] interfaceImplArray;
      private MetaDataMemberRef[] memberRefArray;
      private MetaDataConstant[] constantArray;
      private MetaDataCustomAttribute[] customAttributeArray;
      private MetaDataFieldMarshal[] fieldMarshalArray;
      private MetaDataDeclSecurity[] declSecurityArray;
      private MetaDataClassLayout[] classLayoutArray;
      private MetaDataFieldLayout[] fieldLayoutArray;
      private MetaDataStandAloneSig[] standAloneSigArray;
      private MetaDataEventMap[] eventMapArray;
      private MetaDataEventPtr[] eventPtrArray;
      private MetaDataEvent[] eventArray;
      private MetaDataPropertyMap[] propertyMapArray;
      private MetaDataPropertyPtr[] propertyPtrArray;
      private MetaDataProperty[] propertyArray;
      private MetaDataMethodSemantics[] methodSemanticsArray;
      private MetaDataMethodImpl[] methodImplArray;
      private MetaDataModuleRef[] moduleRefArray;
      private MetaDataTypeSpec[] typeSpecArray;
      private MetaDataImplMap[] implMapArray;
      private MetaDataFieldRVA[] fieldRVAArray;
      private MetaDataAssembly[] assemblyArray;
      private MetaDataAssemblyProcessor[] assemblyProcessorArray;
      private MetaDataAssemblyOS[] assemblyOSArray;
      private MetaDataAssemblyRef[] assemblyRefArray;
      private MetaDataAssemblyRefProcessor[] assemblyRefProcessorArray;
      private MetaDataAssemblyRefOS[] assemblyRefOSArray;
      private MetaDataFile[] fileArray;
      private MetaDataExportedType[] exportedTypeArray;
      private MetaDataManifestResource[] manifestResourceArray;
      private MetaDataNestedClass[] nestedClassArray;
      private MetaDataGenericParam[] genericParamArray;
      private MetaDataMethodSpec[] methodSpecArray;
      private MetaDataGenericParamConstraint[] genericParamConstraintArray;
      private Object[] relocationArray;
      private MetaDataVtableFixup[] vtableFixupArray;
      private MetaDataDelayImportTable delayImportTable;

      private readonly static MetaDataTypeDefinition[] emptyNestedClassArray = new MetaDataTypeDefinition[0];
      private readonly static MetaDataParam[] emptyParamArray = new MetaDataParam[0];
      private readonly static MetaDataField[] emptyFieldArray = new MetaDataField[0];
      private readonly static MetaDataMethod[] emptyMethodArray = new MetaDataMethod[0];
      private readonly static MetaDataObject[] emptyInterfaceArray = new MetaDataObject[0];

      private const int     METAMODEL_MAJOR_VER       = 1;
      private const int     METAMODEL_MINOR_VER_A     = 0;
      private const int     METAMODEL_MINOR_VER_B     = 1;

      private const int     HEAPBITS_MASK_STRINGS     = 0x01;
      private const int     HEAPBITS_MASK_GUID        = 0x02;
      private const int     HEAPBITS_MASK_BLOB        = 0x04;
      private const int     HEAPBITS_MASK_PADDING_BIT = 0x08;
      private const int     HEAPBITS_MASK_DELTA_ONLY  = 0x20;
      private const int     HEAPBITS_MASK_EXTRA_DATA  = 0x40;
      private const int     HEAPBITS_MASK_HAS_DELETE  = 0x80;

      internal static readonly System.Text.UTF8Encoding stringEncoding = new System.Text.UTF8Encoding();

      private static readonly byte[][] TableColumnKinds = new byte[(int) MetaDataTableIndices.Count][] {
          // rModuleCols
          new byte[] { (byte) (byte) ColumnKindId.UShort,
                       (byte) ColumnKindId.String,
                       (byte) ColumnKindId.Guid,
                       (byte) ColumnKindId.Guid,
                       (byte) ColumnKindId.Guid },
          // rTypeRefCols
          new byte[] { (byte) ColumnKindId.CodedToken + (byte) CodeToken.ResolutionScope,
                       (byte) ColumnKindId.String,
                       (byte) ColumnKindId.String },
          // rTypeDefCols
          new byte[] { (byte) ColumnKindId.ULong,
                       (byte) ColumnKindId.String,
                       (byte) ColumnKindId.String,
                       (byte) ColumnKindId.CodedToken + (byte) CodeToken.TypeDefOrRef,
                       (byte) MetaDataTableIndices.Field,
                       (byte) MetaDataTableIndices.Method },
          // rFieldPtrCols
          new byte[] { (byte) MetaDataTableIndices.Field },
          // rFieldCols
          new byte[] { (byte) ColumnKindId.UShort,
                       (byte) ColumnKindId.String,
                       (byte) ColumnKindId.Blob },
          // rMethodPtrCols
          new byte[] { (byte) MetaDataTableIndices.Method },
          // rMethodCols
          new byte[] { (byte) ColumnKindId.ULong,
                       (byte) ColumnKindId.UShort,
                       (byte) ColumnKindId.UShort,
                       (byte) ColumnKindId.String,
                       (byte) ColumnKindId.Blob,
                       (byte) MetaDataTableIndices.Param },
          // rParamPtrCols
          new byte[] { (byte) MetaDataTableIndices.Param },
          // rParamCols
          new byte[] { (byte) ColumnKindId.UShort,
                       (byte) ColumnKindId.UShort,
                       (byte) ColumnKindId.String },
          // rInterfaceImplCols
          new byte[] { (byte) MetaDataTableIndices.TypeDef,
                       (byte) ColumnKindId.CodedToken + (byte) CodeToken.TypeDefOrRef },
          // rMemberRefCols
          new byte[] { (byte) ColumnKindId.CodedToken + (byte) CodeToken.MemberRefParent,
                       (byte) ColumnKindId.String,
                       (byte) ColumnKindId.Blob },
          // rConstantCols
          new byte[] { (byte) ColumnKindId.Byte,
                       (byte) ColumnKindId.CodedToken + (byte) CodeToken.HasConstant,
                       (byte) ColumnKindId.Blob },
          // rCustomAttributeCols
          new byte[] { (byte) ColumnKindId.CodedToken + (byte) CodeToken.HasCustomAttribute,
                       (byte) ColumnKindId.CodedToken + (byte) CodeToken.CustomAttributeType,
                       (byte) ColumnKindId.Blob },
          // rFieldMarshalCols
          new byte[] { (byte) ColumnKindId.CodedToken + (byte) CodeToken.HasFieldMarshal,
                       (byte) ColumnKindId.Blob },
          // rDeclSecurityCols
          new byte[] { (byte) ColumnKindId.Short,
                       (byte) ColumnKindId.CodedToken + (byte) CodeToken.HasDeclSecurity,
                       (byte) ColumnKindId.Blob },
          // rClassLayoutCols
          new byte[] { (byte) ColumnKindId.UShort,
                       (byte) ColumnKindId.ULong,
                       (byte) MetaDataTableIndices.TypeDef },
          // rFieldLayoutCols
          new byte[] { (byte) ColumnKindId.ULong,
                       (byte) MetaDataTableIndices.Field },
          // rStandAloneSigCols
          new byte[] { (byte) ColumnKindId.Blob },
          // rEventMapCols
          new byte[] { (byte) MetaDataTableIndices.TypeDef,
                       (byte) MetaDataTableIndices.Event },
          // rEventPtrCols
          new byte[] { (byte) MetaDataTableIndices.Event },
          // rEventCols
          new byte[] { (byte) ColumnKindId.UShort,
                       (byte) ColumnKindId.String,
                       (byte) ColumnKindId.CodedToken + (byte) CodeToken.TypeDefOrRef },
          // rPropertyMapCols
          new byte[] { (byte) MetaDataTableIndices.TypeDef,
                       (byte) MetaDataTableIndices.Property },
          // rPropertyPtrCols
          new byte[] { (byte) MetaDataTableIndices.Property },
          // rPropertyCols
          new byte[] { (byte) ColumnKindId.UShort,
                       (byte) ColumnKindId.String,
                       (byte) ColumnKindId.Blob },
          // rMethodSemanticsCols
          new byte[] { (byte) ColumnKindId.UShort,
                       (byte) MetaDataTableIndices.Method,
                       (byte) ColumnKindId.CodedToken + (byte) CodeToken.HasSemantic },
          // rMethodImplCols
          new byte[] { (byte) MetaDataTableIndices.TypeDef,
                       (byte) ColumnKindId.CodedToken + (byte) CodeToken.MethodDefOrRef,
                       (byte) ColumnKindId.CodedToken + (byte) CodeToken.MethodDefOrRef },
          // rModuleRefCols
          new byte[] { (byte) ColumnKindId.String },
          // rTypeSpecCols
          new byte[] { (byte) ColumnKindId.Blob },
          // rImplMapCols
          new byte[] { (byte) ColumnKindId.UShort,
                       (byte) ColumnKindId.CodedToken + (byte) CodeToken.MemberForwarded,
                       (byte) ColumnKindId.String,
                       (byte) MetaDataTableIndices.ModuleRef },
          // rFieldRVACols
          new byte[] { (byte) ColumnKindId.ULong,
                       (byte) MetaDataTableIndices.Field },
          // rENCLogCols
          new byte[] { (byte) ColumnKindId.ULong,
                       (byte) ColumnKindId.ULong },
          // rENCMapCols
          new byte[] { (byte) ColumnKindId.ULong },
          // rAssemblyCols
          new byte[] { (byte) ColumnKindId.ULong,
                       (byte) ColumnKindId.UShort,
                       (byte) ColumnKindId.UShort,
                       (byte) ColumnKindId.UShort,
                       (byte) ColumnKindId.UShort,
                       (byte) ColumnKindId.ULong,
                       (byte) ColumnKindId.Blob,
                       (byte) ColumnKindId.String,
                       (byte) ColumnKindId.String },
          // rAssemblyProcessorCols
          new byte[] { (byte) ColumnKindId.ULong },
          // rAssemblyOSCols
          new byte[] { (byte) ColumnKindId.ULong,
                       (byte) ColumnKindId.ULong,
                       (byte) ColumnKindId.ULong },
          // rAssemblyRefCols
          new byte[] { (byte) ColumnKindId.UShort,
                       (byte) ColumnKindId.UShort,
                       (byte) ColumnKindId.UShort,
                       (byte) ColumnKindId.UShort,
                       (byte) ColumnKindId.ULong,
                       (byte) ColumnKindId.Blob,
                       (byte) ColumnKindId.String,
                       (byte) ColumnKindId.String,
                       (byte) ColumnKindId.Blob },
          // rAssemblyRefProcessorCols
          new byte[] { (byte) ColumnKindId.ULong,
                       (byte) MetaDataTableIndices.AssemblyRef },
          // rAssemblyRefOSCols
          new byte[] { (byte) ColumnKindId.ULong,
                       (byte) ColumnKindId.ULong,
                       (byte) ColumnKindId.ULong,
                       (byte) MetaDataTableIndices.AssemblyRef },
          // rFileCols
          new byte[] { (byte) ColumnKindId.ULong,
                       (byte) ColumnKindId.String,
                       (byte) ColumnKindId.Blob },
          // rExportedTypeCols
          new byte[] { (byte) ColumnKindId.ULong,
                       (byte) ColumnKindId.ULong,
                       (byte) ColumnKindId.String,
                       (byte) ColumnKindId.String,
                       (byte) ColumnKindId.CodedToken + (byte) CodeToken.Implementation },
          // rManifestResourceCols
          new byte[] { (byte) ColumnKindId.ULong,
                       (byte) ColumnKindId.ULong,
                       (byte) ColumnKindId.String,
                       (byte) ColumnKindId.CodedToken + (byte) CodeToken.Implementation },
          // rNestedClassCols
          new byte[] { (byte) MetaDataTableIndices.TypeDef,
                       (byte) MetaDataTableIndices.TypeDef },
          // rGenericParamCols
          new byte[] { (byte) ColumnKindId.UShort,
                       (byte) ColumnKindId.UShort,
                       (byte) ColumnKindId.CodedToken + (byte) CodeToken.TypeOrMethodDef,
                       (byte) ColumnKindId.String,
                       (byte) ColumnKindId.CodedToken + (byte) CodeToken.TypeDefOrRef,
                       //                       (byte) ColumnKindId.CodedToken + (byte) CodeToken.TypeDefOrRef
          },
          // rMethodSpecCols
          new byte[] { (byte) ColumnKindId.CodedToken + (byte) CodeToken.MethodDefOrRef,
                       (byte) ColumnKindId.Blob
          },
          // rGenericParamConstraintCols
          new byte[] { (byte) ColumnKindId.CodedToken + (byte) CodeToken.GenericParam,
                       (byte) ColumnKindId.CodedToken + (byte) CodeToken.TypeDefOrRef },
      };

      // These are for informational use only!  Not used anywhere.
      private static readonly String[][] TableColumnNames = new String[(int) MetaDataTableIndices.Count][] {
          // rModuleColNames
          new String[] { "Generation", "Name", "Mvid", "EncId", "EncBaseId" },
          // rTypeRefColNames
          new String[] { "ResolutionScope", "Name", "Namespace" },
          // rTypeDefColNames
          new String[] { "Flags", "Name", "Namespace", "Extends", "FieldList",
                         "MethodList" },
          // rFieldPtrColNames
          new String[] { "Field" },
          // rFieldColNames
          new String[] { "Flags", "Name", "Signature" },
          // rMethodPtrColNames
          new String[] { "Method" },
          // rMethodColNames
          new String[] { "RVA", "ImplFlags", "Flags", "Name", "Signature",
                         "ParamList" },
          // rParamPtrColNames
          new String[] { "Param" },
          // rParamColNames
          new String[] { "Flags", "Sequence", "Name" },
          // rInterfaceImplColNames
          new String[] { "Class", "Interface" },
          // rMemberRefColNames
          new String[] { "Class", "Name", "Signature" },
          // rConstantColNames
          new String[] { "Type", "Parent", "Value" },
          // rCustomAttributeColNames
          new String[] { "Parent", "Type", "Value" },
          // rFieldMarshalColNames
          new String[] { "Parent", "NativeType" },
          // rDeclSecurityColNames
          new String[] { "Action", "Parent", "PermissionSet" },
          // rClassLayoutColNames
          new String[] { "PackingSize", "ClassSize", "Parent" },
          // rFieldLayoutColNames
          new String[] { "OffSet", "Field" },
          // rStandAloneSigColNames
          new String[] { "Signature" },
          // rEventMapColNames
          new String[] { "Parent", "EventList" },
          // rEventPtrColNames
          new String[] { "Event" },
          // rEventColNames
          new String[] { "EventFlags", "Name", "EventType" },
          // rPropertyMapColNames
          new String[] { "Parent", "PropertyList" },
          // rPropertyPtrColNames
          new String[] { "Property" },
          // rPropertyColNames
          new String[] { "PropFlags", "Name", "Type" },
          // rMethodSemanticsColNames
          new String[] { "Semantic", "Method", "Association" },
          // rMethodImplColNames
          new String[] { "Class", "MethodBody", "MethodDeclaration" },
          // rModuleRefColNames
          new String[] { "Name" },
          // rTypeSpecColNames
          new String[] { "Signature" },
          // rImplMapColNames
          new String[] { "MappingFlags", "MemberForwarded", "ImportName",
                         "ImportScope" },
          // rFieldRVAColNames
          new String[] { "RVA", "Field" },
          // rENCLogColNames
          new String[] { "Token", "FuncCode" },
          // rENCMapColNames
          new String[] { "Token" },
          // rAssemblyColNames
          new String[] { "HashAlgId", "MajorVersion", "MinorVersion",
                         "BuildNumber", "RevisionNumber", "Flags",
                         "PublicKey", "Name", "Locale" },
          // rAssemblyProcessorColNames
          new String[] { "Processor" },
          // rAssemblyOSColNames
          new String[] { "OSPlatformId", "OSMajorVersion", "OSMinorVersion" },
          // rAssemblyRefColNames
          new String[] { "MajorVersion", "MinorVersion", "BuildNumber",
                         "RevisionNumber", "Flags", "PublicKeyOrToken",
                         "Name", "Locale", "HashValue" },
          // rAssemblyRefProcessorColNames
          new String[] { "Processor", "AssemblyRef" },
          // rAssemblyRefOSColNames
          new String[] { "OSPlatformId", "OSMajorVersion", "OSMinorVersion",
                         "AssemblyRef" },
          // rFileColNames
          new String[] { "Flags", "Name", "HashValue" },
          // rExportedTypeColNames
          new String[] { "Flags", "TypeDefId", "TypeName", "TypeNamespace",
                         "Implementation" },
          // rManifestResourceColNames
          new String[] { "Offset", "Flags", "Name", "Implementation" },
          // rNestedClassColNames
          new String[] { "NestedClass", "EnclosingClass" },
          // rGenericParamColNames
          new String[] { "Number", "Flags", "Owner", "Name", "Kind" },//, "DeprecatedConstraint" },
          // rMethodSpecNames
          new String[] { "Method", "Instantiation" },
          // rGenericParamConstraintColNames
          new String[] { "Owner", "Constraint" },
      };

      private static readonly int[] BitsForCountArray = new int[] {
          0,1,1,2,2,3,3,3,3,4,4,4,4,4,4,4,4,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5
      };

      private static readonly int[] MaskForCountArray = new int[] {
          0,1,1,3,3,7,7,7,7,0xf,0xf,0xf,0xf,0xf,0xf,0xf,0xf,0x1f,0x1f,0x1f,
          0x1f,0x1f,0x1f,0x1f,0x1f,0x1f,0x1f,0x1f,0x1f,0x1f,0x1f,0x1f,0x1f
      };

      private static readonly TokenType[][] CodeTokenTypeLists = new TokenType[(int) CodeToken.Count][] {
          // TypeDefOrRef
          new TokenType[] { TokenType.TypeDef,
                            TokenType.TypeRef,
                            TokenType.TypeSpec },
          // HasConstant
          new TokenType[] { TokenType.FieldDef,
                            TokenType.ParamDef,
                            TokenType.Property },
          // HasCustomAttribute
          new TokenType[] { TokenType.MethodDef,
                            TokenType.FieldDef,
                            TokenType.TypeRef,
                            TokenType.TypeDef,
                            TokenType.ParamDef,
                            TokenType.InterfaceImpl,
                            TokenType.MemberRef,
                            TokenType.Module,
                            TokenType.Permission,
                            TokenType.Property,
                            TokenType.Event,
                            TokenType.Signature,
                            TokenType.ModuleRef,
                            TokenType.TypeSpec,
                            TokenType.Assembly,
                            TokenType.AssemblyRef,
                            TokenType.File,
                            TokenType.ExportedType,
                            TokenType.ManifestResource},
          // HasFieldMarshal
          new TokenType[] { TokenType.FieldDef,
                            TokenType.ParamDef },
          // HasDeclSecurity
          new TokenType[] { TokenType.TypeDef,
                            TokenType.MethodDef,
                            TokenType.Assembly },
          // MemberRefParent
          new TokenType[] { TokenType.TypeDef,
                            TokenType.TypeRef,
                            TokenType.ModuleRef,
                            TokenType.MethodDef,
                            TokenType.TypeSpec },
          // HasSemantic
          new TokenType[] { TokenType.Event,
                            TokenType.Property },
          // MethodDefOrRef
          new TokenType[] { TokenType.MethodDef,
                            TokenType.MemberRef },
          // MemberForwarded
          new TokenType[] { TokenType.FieldDef,
                            TokenType.MethodDef },
          // Implementation
          new TokenType[] { TokenType.File,
                            TokenType.AssemblyRef,
                            TokenType.ExportedType },
          // CustomAttributeType
          new TokenType[] { TokenType.TypeRef,  // as per 3705: 0
                            TokenType.TypeDef,  // as per 3705: 0
                            TokenType.MethodDef,
                            TokenType.MemberRef,
                            TokenType.String }, // as per 3705: 0
          // ResolutionScope
          new TokenType[] { TokenType.Module,
                            TokenType.ModuleRef,
                            TokenType.AssemblyRef,
                            TokenType.TypeRef },
          // TypeOrMethodDef
          new TokenType[] { TokenType.TypeDef,
                            TokenType.MethodDef },
          // GenericParam
          new TokenType[] { TokenType.GenericParam },
      };

//        static MetaDataLoader() {
//            if ((int) TokenType.Module >> 24           != (int) MetaDataTableIndices.Module ||
//                (int) TokenType.TypeRef >> 24          != (int) MetaDataTableIndices.TypeRef ||
//                (int) TokenType.TypeDef >> 24          != (int) MetaDataTableIndices.TypeDef ||
//                (int) TokenType.FieldDef >> 24         != (int) MetaDataTableIndices.Field ||
//                (int) TokenType.MethodDef >> 24        != (int) MetaDataTableIndices.Method ||
//                (int) TokenType.ParamDef >> 24         != (int) MetaDataTableIndices.Param ||
//                (int) TokenType.InterfaceImpl >> 24    != (int) MetaDataTableIndices.InterfaceImpl ||
//                (int) TokenType.MemberRef >> 24        != (int) MetaDataTableIndices.MemberRef ||
//                (int) TokenType.CustomAttribute >> 24  != (int) MetaDataTableIndices.CustomAttribute ||
//                (int) TokenType.Permission >> 24       != (int) MetaDataTableIndices.DeclSecurity ||
//                (int) TokenType.Signature >> 24        != (int) MetaDataTableIndices.StandAloneSig ||
//                (int) TokenType.Event >> 24            != (int) MetaDataTableIndices.Event ||
//                (int) TokenType.Property >> 24         != (int) MetaDataTableIndices.Property ||
//                (int) TokenType.ModuleRef >> 24        != (int) MetaDataTableIndices.ModuleRef ||
//                (int) TokenType.TypeSpec >> 24         != (int) MetaDataTableIndices.TypeSpec ||
//                (int) TokenType.Assembly >> 24         != (int) MetaDataTableIndices.Assembly ||
//                (int) TokenType.AssemblyRef >> 24      != (int) MetaDataTableIndices.AssemblyRef ||
//                (int) TokenType.File >> 24             != (int) MetaDataTableIndices.File ||
//                (int) TokenType.ExportedType >> 24     != (int) MetaDataTableIndices.ExportedType ||
//                (int) TokenType.ManifestResource >> 24 != (int) MetaDataTableIndices.ManifestResource) {
//                throw new IllegalMetaDataFormatException("TBL invariant broken");
//            }
//            for (int i = 0; i < (int) MetaDataTableIndices.Count; i++) {
//                if (TableColumnKinds[i].Length != TableColumnNames[i].Length) {
//                    throw new IllegalMetaDataFormatException("Column spec mismatch at "+i);
//                }
//            }
//        }

      protected enum MetaDataFormat: byte {
          Invalid, ReadOnly, ReadWrite, ICR
      }

      protected enum MetaDataTableIndices: byte {
          Module,
              TypeRef,
              TypeDef,
              FieldPtr,
              Field,
              MethodPtr,
              Method,
              ParamPtr,
              Param,
              InterfaceImpl,
              MemberRef,
              Constant,
              CustomAttribute,
              FieldMarshal,
              DeclSecurity,
              ClassLayout,
              FieldLayout,
              StandAloneSig,
              EventMap,
              EventPtr,
              Event,
              PropertyMap,
              PropertyPtr,
              Property,
              MethodSemantics,
              MethodImpl,
              ModuleRef,
              TypeSpec,
              ImplMap,
              FieldRVA,
              ENCLog,
              ENCMap,
              Assembly,
              AssemblyProcessor,
              AssemblyOS,
              AssemblyRef,
              AssemblyRefProcessor,
              AssemblyRefOS,
              File,
              ExportedType,
              ManifestResource,
              NestedClass,
              GenericParam,
              MethodSpec,
              GenericParamConstraint,
              Count
      }

      internal enum TokenType: int {
          Module                   = 0x00000000,
              TypeRef              = 0x01000000,
              TypeDef              = 0x02000000,
              FieldDef             = 0x04000000,
              MethodDef            = 0x06000000,
              ParamDef             = 0x08000000,
              InterfaceImpl        = 0x09000000,
              MemberRef            = 0x0a000000,
              CustomAttribute      = 0x0c000000,
              Permission           = 0x0e000000,
              Signature            = 0x11000000,
              Event                = 0x14000000,
              Property             = 0x17000000,
              ModuleRef            = 0x1a000000,
              TypeSpec             = 0x1b000000,
              Assembly             = 0x20000000,
              AssemblyRef          = 0x23000000,
              File                 = 0x26000000,
              ExportedType         = 0x27000000,
              ManifestResource     = 0x28000000,
              GenericParam         = 0x2a000000,
              String               = 0x70000000,
              Name                 = 0x71000000,
              BaseType             = 0x72000000
      };

      private enum ColumnKindId {
          RowIdMax          = 63,
              CodedToken    = 64,
              CodedTokenMax = 95,
              Short         = 96,
              UShort        = 97,
              Long          = 98,
              ULong         = 99,
              Byte          = 100,
              String        = 101,
              Guid          = 102,
              Blob          = 103
      };

      private enum CodeToken: byte {
          TypeDefOrRef,
              HasConstant,
              HasCustomAttribute,
              HasFieldMarshal,
              HasDeclSecurity,
              MemberRefParent,
              HasSemantic,
              MethodDefOrRef,
              MemberForwarded,
              Implementation,
              CustomAttributeType,
              ResolutionScope,
              TypeOrMethodDef,
              GenericParam,
              Count
      };

      private enum SymTag {
          SymTagEnd = -1,
          SymTagFunction,
          SymTagLocal
      };

      // Nested Classes

      private class StorageSignature {

          // Constructor Methods

          internal StorageSignature(Stream stream):
              this(new BinaryReader(stream))
          {
              // Do nothing extra
          }

          internal StorageSignature(BinaryReader reader) {
              this.signature            = reader.ReadInt32();
              this.majorVersion         = reader.ReadInt16();
              this.minorVersion         = reader.ReadInt16();
              this.extraData            = reader.ReadInt32();
              int length = reader.ReadInt32();
              byte[] bytes = new byte[length];
              reader.Read(bytes, 0, length);
              char[] chars = new char[length];
              for (int i = 0; i < length; i++) {
                  chars[i] = (char) bytes[i];
              }
              this.versionString        = new String(chars);
              if (this.signature != StorageSignature.STORAGE_MAGIC_SIG) {
                  throw new IllegalMetaDataFormatException("Don't know signature "+this.signature.ToString("x8"));
              }
              if (this.majorVersion != StorageSignature.FILE_MAJOR_VERSION ||
                  this.minorVersion != StorageSignature.FILE_MINOR_VERSION) {
                  throw new IllegalMetaDataFormatException("Unknown version");
              }
          }

          // State

          internal readonly int signature;
          internal readonly short majorVersion;
          internal readonly short minorVersion;
          internal readonly int extraData;
          internal readonly String versionString;

          private const int STORAGE_MAGIC_SIG      = 0x424A5342;
          private const int FILE_MAJOR_VERSION     = 1;
          private const int FILE_MINOR_VERSION     = 1;

      }

      private class StorageHeader {

          // Constructor Methods

          internal StorageHeader(Stream stream):
              this(new BinaryReader(stream))
          { }

          internal StorageHeader(BinaryReader reader) {
              this.flags = reader.ReadByte();
              this.pad = reader.ReadByte();
              this.streamCount = reader.ReadInt16();
              if ((this.flags & STGHDR_EXTRADATA) != 0) {
                  int count = reader.ReadInt32();
                  reader.ReadBytes(count);
              }
          }

          // State

          internal Byte flags;
          internal Byte pad;
          internal short streamCount;

          internal const Byte STGHDR_EXTRADATA = 0x01;
      }

      private class StorageStream {

          // Constructor Methods

          internal StorageStream(Stream stream):
              this(new BinaryReader(stream))
          { }

          internal StorageStream(BinaryReader reader) {
              this.offset = reader.ReadInt32();
              this.size = reader.ReadInt32();
              byte[] bytes = new byte[4];
              int startIndex = 0;
              bool foundEnd = false;
              while (!foundEnd) {
                  int count = reader.Read(bytes, startIndex, 4);
                  int limit = startIndex + count;
                  for (int i = startIndex; i < limit; i++) {
                      if (bytes[i] == 0) {
                          foundEnd = true;
                          char[] chars = new char[i];
                          for (int j = 0; j < i; j++) {
                              chars[j] = (char) bytes[j];
                          }
                          this.name = new String(chars);
                          break;
                      }
                  }
                  startIndex = limit;
                  if (startIndex == bytes.Length) {
                      byte[] newBytes = new byte[2*startIndex];
                      for (int i = 0; i < startIndex; i++) {
                          newBytes[i] = bytes[i];
                      }
                      bytes = newBytes;
                  }
              }
              while (startIndex % 4 != 0) {
                  startIndex += reader.Read(bytes, 0, startIndex % 4);
              }
          }

          // Output Methods

          public override String ToString() {
              return "StorageStream("+this.name+","+this.offset+","+this.size+")";
          }

          // State

          internal int offset;
          internal int size;
          internal String name;

          internal const String COMPRESSED_MODEL = "#~";
          internal const String ENC_MODEL        = "#-";
          internal const String SCHEMA           = "#Schema";
          internal const String STRING_POOL      = "#Strings";
          internal const String BLOB_POOL        = "#Blob";
          internal const String USER_BLOB_POOL   = "#US";
          internal const String VARIANT_POOL     = "#Variants";
          internal const String GUID_POOL        = "#GUID";

      }

      private class DebugEntry {

          // Constructor Methods

          internal DebugEntry(Stream stream):
              this(new BinaryReader(stream))
          { }

          internal DebugEntry(BinaryReader reader) {
              this.characteristics  = reader.ReadInt32();
              this.timeDateStamp    = reader.ReadInt32();
              this.majorVersion     = reader.ReadInt16();
              this.minorVersion     = reader.ReadInt16();
              this.formatType       = reader.ReadInt32();
              this.sizeOfData       = reader.ReadInt32();
              this.addressOfRawData = reader.ReadInt32();
              this.pointerToRawData = reader.ReadInt32();
          }

          // State

          internal int   characteristics;
          internal int   timeDateStamp;
          internal short majorVersion;
          internal short minorVersion;
          internal int   formatType;
          internal int   sizeOfData;
          internal int   addressOfRawData;
          internal int   pointerToRawData;

      }

      internal class IllegalMetaDataFormatException: Exception {

          internal IllegalMetaDataFormatException(String reason):
              base(reason)
          { }

      }

  }

}
