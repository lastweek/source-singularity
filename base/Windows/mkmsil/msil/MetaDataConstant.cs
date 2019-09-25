// 
// Copyright (c) Microsoft Corporation.   All rights reserved.
//

using System;
using System.IO;

namespace Bartok.MSIL
{

  public class MetaDataConstant: MetaDataObject {

      // Constructor Methods

      internal MetaDataConstant(ElementTypes type, int parentIndex,
                                byte[] valueBuffer) {
          this.type = type;
          this.parentIndex = parentIndex;
          this.valueBuffer = valueBuffer;
      }

      // This is technically not a constructor method, but it is meant to
      // be used to set up the object
      internal void resolveReferences(MetaDataLoader loader) {
          this.parent = loader.getHasConstant(this.parentIndex);
      }

      // Access Methods

      public ElementTypes Type {
          get {
              return this.type;
          }
      }

      // May be one of MetaData{Field,ParamDef,Property}
      public MetaDataObject Parent {
          get {
              return this.parent;
          }
      }

      public byte[] ValueBuffer {
          get {
              return this.valueBuffer;
          }
      }

      public Object Value {
          get {
              return ValueFromBuffer(this.Type, this.ValueBuffer);
          }
      }

      private static Object ValueFromBuffer(ElementTypes type, byte[] buffer) {
          MemoryStream memoryStream = new MemoryStream(buffer);
          BinaryReader binaryReader =
              new BinaryReader(memoryStream, System.Text.Encoding.Unicode);
          switch (type) {
            case ElementTypes.BOOLEAN:
                return binaryReader.ReadBoolean();
            case ElementTypes.CHAR:
                return (char) binaryReader.ReadUInt16();
            case ElementTypes.I1:
                return binaryReader.ReadSByte();
            case ElementTypes.U1:
                return binaryReader.ReadByte();
            case ElementTypes.I2:
                return binaryReader.ReadInt16();
            case ElementTypes.U2:
                return binaryReader.ReadUInt16();
            case ElementTypes.I4:
                return binaryReader.ReadInt32();
            case ElementTypes.U4:
                return binaryReader.ReadUInt32();
            case ElementTypes.I8:
                return binaryReader.ReadInt64();
            case ElementTypes.U8:
                return binaryReader.ReadUInt64();
            case ElementTypes.R4:
                return binaryReader.ReadSingle();
            case ElementTypes.R8:
                return binaryReader.ReadDouble();
            case ElementTypes.STRING: {
                char[] chars =
                    binaryReader.ReadChars(buffer.Length/2);
                return new String(chars);
            }
            default:
                throw new MetaDataLoader.IllegalMetaDataFormatException("Unknown type of constant: "+type);
          }
      }

      // Debug Methods

      public override String ToString() {
          System.Text.StringBuilder sb =
              new System.Text.StringBuilder("MetaDataConstant(");
          sb.Append(this.type);
          sb.Append(",");
          if (this.parent == null) {
              sb.Append(this.parentIndex);
          }
          else {
              sb.Append(this.parent);
          }
          sb.Append(",");
          sb.Append(this.Value);
          sb.Append(")");
          return sb.ToString();
      }

      // State

      private readonly ElementTypes   type;
      private readonly int            parentIndex;
      private          MetaDataObject parent;
      private readonly byte[]         valueBuffer;

  }

}
