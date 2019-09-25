// 
// Copyright (c) Microsoft Corporation.   All rights reserved.
//

namespace Bartok.MSIL
{

  using System;

  public abstract class MarshalSpec {

      // Constructor Methods

      internal static MarshalSpec Create(byte[] buffer) {
          int offset = 0;
          NativeTypes kind = (NativeTypes)
              SignatureBuffer.uncompressInt(buffer, ref offset);
          switch (kind) {
            case NativeTypes.BOOLEAN:
            case NativeTypes.I1:
            case NativeTypes.U1:
            case NativeTypes.I2:
            case NativeTypes.U2:
            case NativeTypes.I4:
            case NativeTypes.U4:
            case NativeTypes.I8:
            case NativeTypes.U8:
            case NativeTypes.R4:
            case NativeTypes.R8:
            case NativeTypes.CURRENCY:
            case NativeTypes.BSTR:
            case NativeTypes.LPSTR:
            case NativeTypes.LPWSTR:
            case NativeTypes.LPTSTR:
            case NativeTypes.IUNKNOWN:
            case NativeTypes.IDISPATCH:
            case NativeTypes.STRUCT:
            case NativeTypes.INTF:
            case NativeTypes.INT:
            case NativeTypes.UINT:
            case NativeTypes.BYVALSTR:
            case NativeTypes.ANSIBSTR:
            case NativeTypes.TBSTR:
            case NativeTypes.VARIANTBOOL:
            case NativeTypes.FUNC:
            case NativeTypes.ASANY:
            case NativeTypes.LPSTRUCT:
            case NativeTypes.ERROR:
            case NativeTypes.MAX: {
                if (offset != buffer.Length) {
                    Console.WriteLine("WARNING: extra bytes in "+new MetaDataBlob(buffer));
                }
                return new MarshalSpecNative(kind);
            }
            case NativeTypes.SAFEARRAY: {
                VariantTypes elemType;
                if (offset < buffer.Length) {
                    elemType = (VariantTypes)
                        SignatureBuffer.uncompressInt(buffer, ref offset);
                }
                else {
                    elemType = VariantTypes.VT_EMPTY;
                }
                if (offset != buffer.Length) {
                    Console.WriteLine("WARNING: extra bytes in "+new MetaDataBlob(buffer));
                }
                return new MarshalSpecSafeArray(elemType);
            }
            case NativeTypes.FIXEDSYSSTRING: {
                uint elemCount =
                    SignatureBuffer.uncompressInt(buffer, ref offset);
                if (offset != buffer.Length) {
                    Console.WriteLine("WARNING: extra bytes in "+new MetaDataBlob(buffer));
                }
                return new MarshalSpecFixedString(elemCount);
            }
            case NativeTypes.FIXEDARRAY: {
                uint elemCount =
                    SignatureBuffer.uncompressInt(buffer, ref offset);
                if (offset != buffer.Length) {
                    Console.WriteLine("WARNING: extra bytes in "+new MetaDataBlob(buffer));
                }
                return new MarshalSpecFixedArray(elemCount);
            }
            case NativeTypes.CUSTOMMARSHALER: {
                String guid = uncompressString(buffer, ref offset);
                String unmanagedType = uncompressString(buffer, ref offset);
                String managedType = uncompressString(buffer, ref offset);
                String cookie = uncompressString(buffer, ref offset);
                if (offset != buffer.Length) {
                    Console.WriteLine("WARNING: extra bytes in "+new MetaDataBlob(buffer));
                }
                return new MarshalSpecCustom(guid, unmanagedType,
                                             managedType, cookie);
            }
            case NativeTypes.ARRAY: {
                NativeTypes elemType = (NativeTypes)
                    SignatureBuffer.uncompressInt(buffer, ref offset);
                uint paramNumber =
                    ((offset < buffer.Length) ?
                     SignatureBuffer.uncompressInt(buffer, ref offset) :
                     0); 
                uint extras =
                    ((offset < buffer.Length) ?
                     SignatureBuffer.uncompressInt(buffer, ref offset) :
                     0);
                if (offset != buffer.Length) {
                    Console.WriteLine("WARNING: extra bytes in "+new MetaDataBlob(buffer));
                }
                return new MarshalSpecArray(elemType, paramNumber, extras);
            }
            default: {
                throw new Exception("Unknown marshal spec kind "+kind);
            }
          }
      }

      private static String uncompressString(byte[] buffer, ref int offset) {
          uint length = SignatureBuffer.uncompressInt(buffer, ref offset);
          int oldOffset = offset;
          offset += (int) length;
          return MetaDataLoader.stringEncoding.GetString(buffer, oldOffset,
                                                         (int) length);
      }

      public override abstract String ToString();

  }

  public class MarshalSpecNative: MarshalSpec {

      // Constructor Methods

      public MarshalSpecNative(NativeTypes kind) {
          this.kind = kind;
      }

      // Accessors

      public NativeTypes Kind {
          get { return this.kind; }
      }

      public override String ToString() {
          return "MarshalSpecNative("+kind+")";
      }

      // Private State

      private readonly NativeTypes kind;

  }

  public class MarshalSpecSafeArray: MarshalSpec {

      // Constructor Methods

      public MarshalSpecSafeArray(VariantTypes elemType) {
          this.elemType = elemType;
      }

      // Accessors

      public VariantTypes ElementType {
          get { return this.elemType; }
      }

      public override String ToString() {
          return "MarshalSpecSafeArray("+elemType+")";
      }

      // Private State

      private readonly VariantTypes elemType;

  }

  public class MarshalSpecFixedString: MarshalSpec {

      // Constructor Methods

      public MarshalSpecFixedString(uint elemCount) {
          this.elemCount = elemCount;
      }

      // Accessors

      public uint ElementCount {
          get { return this.elemCount; }
      }

      public override String ToString() {
          return "MarshalSpecFixedString("+elemCount+")";
      }

      // Private State

      private readonly uint elemCount;

  }

  public class MarshalSpecFixedArray: MarshalSpec {

      // Constructor Methods

      public MarshalSpecFixedArray(uint elemCount) {
          this.elemCount = elemCount;
      }

      // Accessors

      public uint ElementCount {
          get { return this.elemCount; }
      }

      public override String ToString() {
          return "MarshalSpecFixedArray("+elemCount+")";
      }

      // Private State

      private readonly uint elemCount;

  }

  public class MarshalSpecCustom: MarshalSpec {

      // Constructor Methods

      public MarshalSpecCustom(String guid, String unmanagedType,
                               String managedType, String cookie) {
          this.guid = guid;
          this.unmanagedType = unmanagedType;
          this.managedType = managedType;
          this.cookie = cookie;
      }

      // Accessors

      public String Guid {
          get { return this.guid; }
      }

      public String UnmanagedType {
          get { return this.unmanagedType; }
      }

      public String ManagedType {
          get { return this.managedType; }
      }

      public String Cookie {
          get { return this.cookie; }
      }

      public override String ToString() {
          return ("MarshalSpecCustom("+guid+","+
                  managedType+"->"+unmanagedType+","+cookie+")");
      }

      // Private State

      private readonly String guid;
      private readonly String unmanagedType;
      private readonly String managedType;
      private readonly String cookie;

  }

  public class MarshalSpecArray: MarshalSpec {

      // Constructor Methods

      public MarshalSpecArray(NativeTypes elemType, uint paramNumber,
                              uint extras) {
          this.elemType = elemType;
          this.paramNumber = paramNumber;
          this.extras = extras;
      }

      // Accessors

      public NativeTypes ElementType {
          get { return this.elemType; }
      }

      public uint ParameterNumber {
          get { return this.paramNumber; }
      }

      public uint ExtraCount {
          get { return this.extras; }
      }

      public override String ToString() {
          return "MarshalSpecArray("+elemType+","+paramNumber+","+extras+")";
      }

      // Private State

      private readonly NativeTypes elemType;
      private readonly uint paramNumber;
      private readonly uint extras;

  }

}
