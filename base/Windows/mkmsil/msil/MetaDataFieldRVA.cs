//
// Copyright (c) Microsoft Corporation.   All rights reserved.
//

using System;
using System.IO;

namespace Bartok.MSIL
{

  using System.Reflection;

  public class MetaDataFieldRVA: MetaDataObject {

      // Constructor Methods

      internal MetaDataFieldRVA(int rva, MetaDataField field) {
          this.rva = rva;
          this.field = field;
      }

      internal void resolveReferences(MetaDataLoader loader,
                                      PELoader peLoader,
                                      Stream fileStream) {
          this.field.resolveReferences(this);
          int dataOffset = peLoader.VaToOffsetSafe(this.rva);
          if (dataOffset != -1) {
              fileStream.Seek(dataOffset, SeekOrigin.Begin);
              BinaryReader reader = new BinaryReader(fileStream);
              SignatureField fieldSignature = (SignatureField)
                  this.field.Signature;
              Signature.Type fieldType = fieldSignature.FieldType;
              int dataSize = this.getFieldSize(fieldType);
              byte[] data = new byte[dataSize];
              int count = reader.Read(data, 0, dataSize);
              if (loader.HasVtableFixup() &&
                  loader.RVAHasRelocation(dataOffset) &&
                  dataSize == 4) {
                  // if this corresponds to a vtable label, we need to fix it
                  int location = data[0] | (data[1] << 8) |
                      (data[2] << 16) | (data[3] << 24);
                  int imageBase = peLoader.getImageBase();
                  location -= imageBase;  // use RVA
                  fileStream.Seek(location, SeekOrigin.Begin);
                  BinaryReader binaryReader = new BinaryReader(fileStream);
                  short prefix = binaryReader.ReadInt16();
                  if (prefix == 0x25FF) { // this starts a vtable lable
                      count  = binaryReader.Read(data, 0, 4);
                  }
              }
              this.dataBytes = data;

              if (count != dataSize) {
                  throw new MetaDataLoader.IllegalMetaDataFormatException("Only got "+count+" out of "+dataSize+" data bytes for FieldRVA "+this.rva);
              }
          }
          else {
              Console.WriteLine("Found no data for "+this.field);
          }
      }


      // Access Methods

      public byte[] DataBytes {
          get {
              return this.dataBytes;
          }
      }

      public MetaDataField Field {
          get {
              return this.field;
          }
      }

      public int RVA {
          get {
              return this.rva;
          }
      }

      // Helper Methods

      private int getFieldSize(Signature.Type fieldType) {
          switch (fieldType.ElementType) {
            case ElementTypes.VOID:
                return 0;
            case ElementTypes.BOOLEAN:
            case ElementTypes.I1:
            case ElementTypes.U1:
                return 1;
            case ElementTypes.CHAR:
            case ElementTypes.I2:
            case ElementTypes.U2:
                return 2;
            case ElementTypes.I4:
            case ElementTypes.U4:
            case ElementTypes.R4:
                return 4;
            case ElementTypes.I8:
            case ElementTypes.U8:
            case ElementTypes.R8:
                return 8;
            case ElementTypes.OBJECT:
            case ElementTypes.STRING:
            case ElementTypes.FNPTR:
            case ElementTypes.CLASS:
            case ElementTypes.PTR:
            case ElementTypes.BYREF:
            case ElementTypes.U:
            case ElementTypes.I:
                return machineIntSize;
            case ElementTypes.TYPEDBYREF:
                return 2*machineIntSize;
            case ElementTypes.VALUETYPE: {
                MetaDataObject classObject = fieldType.ClassObject;
                if (!(classObject is MetaDataTypeDefinition)) {
                    return -1;
                }
                MetaDataTypeDefinition typedef = (MetaDataTypeDefinition) classObject;
                if ((typedef.Flags & TypeAttributes.Interface) != 0 ||
                    (typedef.Flags & TypeAttributes.Abstract) != 0) {
                    return -1;
                }
                int classSize = 0;
                int packSize = 0;
                if (typedef.ClassLayout != null) {
                    classSize = typedef.ClassLayout.ClassSize;
                    packSize = typedef.ClassLayout.PackingSize;
                }
                int instanceFieldSize = 0;
                if ((typedef.Flags & TypeAttributes.ExplicitLayout) != 0) {
                    foreach (MetaDataField mdField in typedef.Fields) {
                        if ((mdField.Flags & (int) MetaDataField.FieldAttributes.Static) == 0) {
                            Signature.Type nestedFieldType =
                                ((SignatureField) mdField.Signature).FieldType;
                            int fieldSize = this.getFieldSize(nestedFieldType);
                            int offset = mdField.Layout.Offset;
                            int fieldEnd = fieldSize + offset;
                            if (fieldEnd > instanceFieldSize) {
                                instanceFieldSize = fieldEnd;
                            }
                        }
                    }
                }
                else {
                    foreach (MetaDataField mdField in typedef.Fields) {
                        if ((mdField.Flags & (int) MetaDataField.FieldAttributes.Static) == 0) {
                            Signature.Type nestedFieldType =
                                ((SignatureField) mdField.Signature).FieldType;
                            int fieldSize = this.getFieldSize(nestedFieldType);
                            if (fieldSize == -1) {
                                return -1;
                            }
                            if (packSize > 1) {
                                int delta = instanceFieldSize % packSize;
                                if (delta > 0) {
                                    instanceFieldSize += packSize - delta;
                                }
                            }
                            instanceFieldSize += fieldSize;
                        }
                    }
                }
                if (instanceFieldSize > classSize) {
                    return instanceFieldSize;
                }
                else if (classSize > 0) {
                    return classSize;
                }
                else {
                    return 1;
                }
            }
            case ElementTypes.ARRAY: {
                int elementCount = 1;
                uint[] lowerBounds = fieldType.LowerBounds;
                uint[] upperBounds = fieldType.UpperBounds;
                int rank = upperBounds.Length;
                for (int i = 0; i < rank; i++) {
                    int dimSize = (int) (upperBounds[i] - lowerBounds[i]);
                    if (dimSize == 0) {
                        // Must be an array of pointers to other arrays
                        return elementCount * machineIntSize;
                    }
                    else {
                        elementCount *= dimSize;
                    }
                }
                int elementSize = this.getFieldSize(fieldType.TypeObject);
                return elementCount * elementSize;
            }
            case ElementTypes.CMOD_REQD:
            case ElementTypes.CMOD_OPT:
                return this.getFieldSize(fieldType.TypeObject);
            case ElementTypes.PINNED:
                return this.getFieldSize(fieldType.TypeObject);
            case ElementTypes.SZARRAY:
                // Should be machine dependent!
                return 4;
            case ElementTypes.SENTINEL:
            case ElementTypes.END:
            default:
                return -1;
          }
      }

      // Debug Methods

      public override String ToString() {
          System.Text.StringBuilder sb =
              new System.Text.StringBuilder("MetaDataFieldRVA(");
          sb.Append(this.field);
          sb.Append(",");
          if (this.dataBytes == null) {
              sb.Append(this.rva);
          }
          else {
              sb.Append("[");
              int count = this.dataBytes.Length;
              if (count > 0) {
                  sb.Append(this.dataBytes[0].ToString("x2"));
                  for (int i = 1; i < count; i++) {
                      sb.Append(",");
                      sb.Append(this.dataBytes[i].ToString("x2"));
                  }
              }
              sb.Append("]");
          }
          sb.Append(")");
          return sb.ToString();
      }

      // State

      private readonly int           rva;
      private          byte[]        dataBytes;
      private readonly MetaDataField field;

      // BUGBUG: Should be machine dependent!
      private const int machineIntSize = 4;

  }

}
