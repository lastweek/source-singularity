// 
// Copyright (c) Microsoft Corporation.   All rights reserved.
//

using System;
using System.Text;

///////////////////////////////////////////////////////////////////////
//
// The Bartok.msil.Signature* classes represent the signatures read
// from the Blob heap of the input file(s).
// 
// Since the signatures have references to MetaData* objects, the
// signatures are initially just an array of bytes.  When all the
// MetaData objects have been created, the array of bytes is processed
// and the references resolved.
//
//////////////////////////////////////////////////////////////////////  

namespace Bartok.MSIL
{

  public abstract class Signature {

      // Constructor Methods

      internal virtual Signature resolve(MetaDataLoader mdLoader) {
          return this;
      }

      internal virtual Signature resolveTypeSpec(MetaDataLoader mdLoader) {
          return this;
      }

      // Internal Classes

      public enum CallingConventions: byte {
          Default                = 0x00,
              Unmanaged_cdecl    = 0x01,
              Unmanaged_sdtcall  = 0x02,
              Unmanaged_thiscall = 0x03,
              Unmanaged_fastcall = 0x04,
              VarArg             = 0x05,
              Field              = 0x06,
              LocalVar           = 0x07,
              Property           = 0x08,
              Unmanaged          = 0x09,
              Mask               = 0x0f,
              Generic            = 0x10,
              HasThis            = 0x20,
              ExplicitThis       = 0x40
      }

      // REVIEW: Consider memoizing these types.

      public class Type {

          // Constructor Methods

          // elementType \in
          // { VOID, BOOLEAN, CHAR, I1, U1, I2, U2, I4, U4, I8, U8, R4, R8,
          //   U, I, OBJECT, STRING, TYPEDBYREF }
          internal Type(ElementTypes elementType) {
              this.elementType = elementType;
          }

          // elementType \in {VALUETYPE, CLASS}
          internal Type(ElementTypes elementType,
                        MetaDataObject classObject) {
              this.elementType = elementType;
              this.classObject = classObject;
          }

          // elementType \in {SZARRAY, CMOD_OPT, CMOD_REQD, PINNED, PTR, BYREF}
          internal Type(ElementTypes elementType,
                        Type typeObject,
                        Modifier modifierList) {
              this.elementType = elementType;
              this.typeObject = typeObject;
              this.modifierList = modifierList;
          }
          
          // elementType is ARRAY
          internal Type(ElementTypes elementType,
                        Type typeObject,
                        uint[] lowerBounds,
                        uint[] upperBounds) {
              this.elementType = elementType;
              this.typeObject = typeObject;
              this.lowerBounds = lowerBounds;
              this.upperBounds = upperBounds;
          }

          // elementType is FNPTR
          internal Type(ElementTypes elementType,
                        SignatureMethod methodSignature) {
              this.elementType = elementType;
              this.methodSignature = methodSignature;
          }

          // elementType \in {VAR, MVAR}
          internal Type(ElementTypes elementType,
                        uint number) {
              this.elementType = elementType;
              this.number = number;
          }

          // elementType is GENERICINST
          internal Type(ElementTypes elementType,
                        Type typeObject,
                        Type[] typeList) {
              this.elementType = elementType;
              this.typeObject = typeObject;
              this.typeList = typeList;
          }

          // Accessors

          public ElementTypes ElementType {
              get { return elementType; }
          }

          public MetaDataObject ClassObject {
              // REVIEW: throw on inconsistent elementtype?
              get { return classObject; }
          }

          public Type TypeObject {
              // REVIEW: throw on inconsistent elementtype?
              get { return typeObject; }
          }

          public Type[] TypeList {
              // REVIEW: throw on inconsistent elementtype?
              get { return typeList; }
          }

          public Modifier ModifierList {
              // REVIEW: throw on inconsistent elementtype?
              get { return modifierList; }
          }

          public uint[] UpperBounds {
              // REVIEW: throw on inconsistent elementtype?
              get { return upperBounds; }
          }

          public uint[] LowerBounds {
              // REVIEW: throw on inconsistent elementtype?
              get { return lowerBounds; }
          }
          
          public int Rank {
              get { return upperBounds.Length; }
          }

          public SignatureMethod MethodSignature {
              // REVIEW: throw on inconsistent elementtype?
              get { return methodSignature; }
          }

          public uint Number {
              // REVIEW: throw on inconsistent elementtype?
              get { return number; }
          }

#region SyncBlockHack
          // Equality methods

          public override bool Equals(Object o) {
              return this == o;
          }

          public override int GetHashCode() {
              if (hash == 0) {
                  if (nextHash == 0) {
                      nextHash++;
                  }
                  hash = nextHash++;
              }
              return hash;
          }
#endregion
              
          // Debug Methods

          public override string ToString() {
              StringBuilder sb = new StringBuilder("Type(0x");
              // BUGBUG: use symbolic printing when selfhost can do so
              sb.Append(((uint) elementType).ToString("x"));
              sb.Append(",");
              for (Modifier modifier = this.modifierList;
                   modifier != null;
                   modifier = modifier.next) {
                  sb.Append(modifier);
                  sb.Append(",");
              }
              if (this.typeObject != null) {
                  sb.Append(this.typeObject);
                  sb.Append(",");
              }
              if (this.typeList != null) {
                  sb.Append("typelist[");
                  sb.Append(this.typeList[0]);
                  for (int i = 1; i < this.typeList.Length; i++) {
                      sb.Append(",");
                      sb.Append(this.typeList[i]);
                  }
                  sb.Append("],");
              }
              if (this.classObject != null) {
                  sb.Append(this.classObject);
                  sb.Append(",");
              }
              if (this.lowerBounds != null) {
                  sb.Append("lowerbounds[");
                  sb.Append(this.lowerBounds[0]);
                  for (int i = 1; i < this.lowerBounds.Length; i++) {
                      sb.Append(",");
                      sb.Append(this.lowerBounds[i]);
                  }
                  sb.Append("],");
              }
              if (this.upperBounds != null) {
                  sb.Append("upperbounds[");
                  sb.Append(this.upperBounds[0]);
                  for (int i = 1; i < this.upperBounds.Length; i++) {
                      sb.Append(",");
                      sb.Append(this.upperBounds[i]);
                  }
                  sb.Append("],");
              }
              if (this.methodSignature != null) {
                  sb.Append(methodSignature);
                  sb.Append(",");
              }
              if (this.elementType == ElementTypes.VAR
                  || this.elementType == ElementTypes.MVAR) {
                  sb.Append(number);
                  sb.Append(",");
              }
              sb.Remove(sb.Length-1, 1);
              sb.Append(")");
              return sb.ToString();
          }

          // State

          private readonly ElementTypes elementType;
          private readonly MetaDataObject classObject;
          private readonly Type typeObject;
          private readonly Type[] typeList;
          private readonly Modifier modifierList;
          private readonly uint[] lowerBounds;
          private readonly uint[] upperBounds;
          private readonly SignatureMethod methodSignature;
          private readonly uint number;

#region SyncBlockHack
          private int hash;
          private static int nextHash;
#endregion
      }

      public class Param {

          // Constructor Methods

          internal Param(Modifier modifierList, ElementTypes kind, Type type) {
              this.modifierList = modifierList;
              this.kind = kind;
              this.type = type;
          }

          // Access Methods

          public Modifier ModifierList {
              get {
                  return this.modifierList;
              }
          }

          // One of ElementTypes.{END, BYREF, TYPEDBYREF},
          // ElementTypes.END means no flag present
          public ElementTypes Kind {
              get {
                  return this.kind;
              }
          }

          public Type Type {
              get {
                  return this.type;
              }
          }

          // Debug Methods

          public override string ToString() {
              StringBuilder sb = new StringBuilder("Parameter(");
              for (Modifier modifier = this.modifierList;
                   modifier != null;
                   modifier = modifier.next) {
                  sb.Append(modifier);
                  sb.Append(",");
              }
              sb.Append(((uint) kind).ToString("x"));
              sb.Append(",");
              sb.Append(type);
              sb.Append(")");
              return sb.ToString();
          }

          // State

          private readonly Modifier modifierList;
          private readonly ElementTypes kind;
          private readonly Type type;

      }

      public class Modifier {

          // Constructor Methods

          internal Modifier(ElementTypes kind,
                            MetaDataObject type,
                            Modifier next) {
              this.kind = kind;
              this.type = type;
              this.next = next;
          }

          // Accessor
          public ElementTypes Kind {
              get { return kind; }
          }

          public MetaDataObject Type {
              get { return type; }
          }

          public Modifier Next {
              get { return next; }
          }

          // Debug Methods

          public override string ToString() {
              return (((uint) kind).ToString("x")+" "+type);
          }

          // State

          private  readonly ElementTypes   kind;
          private  readonly MetaDataObject type;
          internal readonly Modifier       next;

      }

  }

  internal class SignatureBuffer: Signature {

      // Constructor Methods

      internal SignatureBuffer(byte[] buffer) {
          this.buffer = buffer;
      }

      internal override Signature resolve(MetaDataLoader mdLoader) {
          uint unmaskedCallingConvention =
              uncompressInt(this.buffer, ref this.offset);
          CallingConventions callingConvention = (CallingConventions)
              (unmaskedCallingConvention & (uint) CallingConventions.Mask);
          switch (callingConvention) {
            case CallingConventions.Field: {
                // Section 22.2.4 of ECMA spec, partition II
                Type type = this.parseSignatureType(mdLoader);
                if (this.offset != this.buffer.Length) {
                    throw new MetaDataLoader.IllegalMetaDataFormatException("Only read "+this.offset+" bytes of "+this);
                }
                return new SignatureField(type);
            }
            case CallingConventions.LocalVar: {
                // Section 22.2.6 of ECMA spec, partition II
                uint count = uncompressInt(this.buffer, ref this.offset);
                Type[] locals = new Type[count];
                for (int i = 0; i < count; i++) {
                    locals[i] = parseSignatureLocal(mdLoader);
                }
                if (this.offset != this.buffer.Length) {
                    throw new MetaDataLoader.IllegalMetaDataFormatException("Only read "+this.offset+" bytes of "+this);
                }
                return new SignatureLocalVar(locals);
            }
            case CallingConventions.Property: {
                // Section 22.2.5 of ECMA spec, partition II
                uint paramCount = uncompressInt(this.buffer, ref this.offset);
                Type returnType = this.parseSignatureType(mdLoader);
                Param[] parameters = new Param[paramCount];
                for (int i = 0; i < paramCount; i++) {
                    parameters[i] = this.parseSignatureParam(mdLoader);
                }
                if (this.offset != this.buffer.Length) {
                    throw new MetaDataLoader.IllegalMetaDataFormatException("Only read "+this.offset+" bytes of "+this);
                }
                return new SignatureProperty(returnType, parameters);
            }
            default: {
                // Section2 22.2.1, 22.2.2, and 22.2.3 of ECMA spec, II
                uint genericParamCount = 0;
                if((unmaskedCallingConvention
                    & (uint) CallingConventions.Generic) != 0) {
                    genericParamCount = uncompressInt(this.buffer,
                                                      ref this.offset);
                }
                uint paramCount = uncompressInt(this.buffer, ref this.offset);
                Type returnType = this.parseSignatureType(mdLoader);
                int sentinelLocation = -1;
                Param[] parameters = new Param[paramCount];
                for (int i = 0; i < paramCount; i++) {
                    byte first = this.buffer[this.offset];
                    if (first == (byte) ElementTypes.SENTINEL) {
                        sentinelLocation = i;
                        this.offset++;
                    }
                    parameters[i] = this.parseSignatureParam(mdLoader);
                }
                if (this.offset != this.buffer.Length) {
                    throw new MetaDataLoader.IllegalMetaDataFormatException("Only read "+this.offset+" bytes of "+this);
                }
                // pass unmasked convention because user of signature (e.g. memberRef)
                // may need to know the static vs. instance status of the method
                // Erik, 4/13/01
                return new SignatureMethod((CallingConventions)
                                           unmaskedCallingConvention,
                                           genericParamCount,
                                           returnType, parameters,
                                           sentinelLocation);
            }
          }

      }

      internal override Signature resolveTypeSpec(MetaDataLoader mdLoader) {
          Type type = this.parseSignatureType(mdLoader);
          if (this.offset != this.buffer.Length) {
              throw new MetaDataLoader.IllegalMetaDataFormatException("Only read "+this.offset+" bytes of "+this);
          }
          return new SignatureTypeSpec(type);
      }

      internal static uint uncompressInt(byte[] buffer, ref int offset) {
          byte first = buffer[offset];
          if ((first & 0x80) == 0x00) {
              // 0??? ????: one byte encoding
              offset++;
              return first;
          }
          else if ((first & 0xC0) == 0x80) {
              // 10?? ????: two byte encoding
              byte second = buffer[offset+1];
              offset += 2;
              return (((first & 0x3fU) << 8) | second);
          }
          else {
              // 11?? ????: four byte encoding
              byte second = buffer[offset+1];
              byte third = buffer[offset+2];
              byte fourth = buffer[offset+3];
              offset += 4;
              return (((uint) ((first & 0x3fU) << 24)) |
                      ((uint) (second << 16)) |
                      ((uint) (third << 8)) |
                      ((uint) fourth));
          }
      }

      private MetaDataObject uncompressToken(MetaDataLoader mdLoader) {
          uint codedToken = uncompressInt(this.buffer, ref this.offset);
          MetaDataLoader.TokenType tokenType =
              ((((codedToken & 0x2) == 0) ?
                (((codedToken & 0x1) == 0) ?
                 MetaDataLoader.TokenType.TypeDef :
                 MetaDataLoader.TokenType.TypeRef) :
                (((codedToken & 0x1) == 0) ?
                 MetaDataLoader.TokenType.TypeSpec :
                 MetaDataLoader.TokenType.BaseType)));
          int token = (int) (codedToken >> 2) | (int) tokenType;
          return mdLoader.getObjectFromToken(token);
      }

      private Type parseSignatureType(MetaDataLoader mdLoader) {
          ElementTypes elementType = (ElementTypes) this.buffer[this.offset];
          this.offset++;
          switch (elementType) {
            case ElementTypes.VOID:
            case ElementTypes.BOOLEAN:
            case ElementTypes.CHAR:
            case ElementTypes.I1:
            case ElementTypes.U1:
            case ElementTypes.I2:
            case ElementTypes.U2:
            case ElementTypes.I4:
            case ElementTypes.U4:
            case ElementTypes.I8:
            case ElementTypes.U8:
            case ElementTypes.R4:
            case ElementTypes.R8:
            case ElementTypes.U:
            case ElementTypes.I:
            case ElementTypes.OBJECT:
            case ElementTypes.STRING:
            case ElementTypes.TYPEDBYREF: {
                return new Type(elementType);
            }
            case ElementTypes.VALUETYPE:
            case ElementTypes.CLASS: {
                // Followed by: TypeDefOrRefEncoded
                MetaDataObject classObject = uncompressToken(mdLoader);
                return new Type(elementType, classObject);
            }
            case ElementTypes.SZARRAY: {
                // Followed by: CustomMod* Type
                Modifier modifierList = this.parseSignatureModifiers(mdLoader);
                Type type = this.parseSignatureType(mdLoader);
                return new Type(elementType, type, modifierList);
            }
            case ElementTypes.ARRAY: {
                // Followed by: Type ArrayShape
                Type type = this.parseSignatureType(mdLoader);
                uint rank = uncompressInt(this.buffer, ref this.offset);
                if (rank == 0) {
                    throw new MetaDataLoader.IllegalMetaDataFormatException("ARRAY with rank 0");
                }
                uint[] upperBounds = new uint[rank];
                uint[] lowerBounds = new uint[rank];
                uint numUpperBounds =
                    uncompressInt(this.buffer, ref this.offset);
                if (numUpperBounds > rank) {
                    throw new MetaDataLoader.IllegalMetaDataFormatException("ARRAY with upper bounds > rank");
                }
                for (int i = 0; i < numUpperBounds; i++) {
                    upperBounds[i] =
                        uncompressInt(this.buffer, ref this.offset);
                }
                uint numLowerBounds =
                    uncompressInt(this.buffer, ref this.offset);
                if (numLowerBounds > rank) {
                    throw new MetaDataLoader.IllegalMetaDataFormatException("ARRAY with lower bounds > rank");
                }
                for (int i = 0; i < numLowerBounds; i++) {
                    lowerBounds[i] =
                        uncompressInt(this.buffer, ref this.offset);
                }
                return new Type(elementType, type, lowerBounds, upperBounds);
            }
            case ElementTypes.FNPTR: {
                // Followed by: MethodDefSig or MethodRefSig
                uint unmaskedCallingConvention =
                    uncompressInt(this.buffer, ref this.offset);
                CallingConventions callingConvention = (CallingConventions)
                    (unmaskedCallingConvention
                     & (uint) CallingConventions.Mask);
                if (callingConvention == CallingConventions.Field ||
                    callingConvention == CallingConventions.LocalVar ||
                    callingConvention == CallingConventions.Property) {
                    throw new MetaDataLoader.IllegalMetaDataFormatException("FNPTR surprised by calling convention "+callingConvention);
                }
                if ((unmaskedCallingConvention
                     & (uint) CallingConventions.Generic) != 0) {
                    throw new MetaDataLoader.IllegalMetaDataFormatException("FNPTR generic unimplemented - check to see if legal");
                }
                uint paramCount = uncompressInt(this.buffer, ref this.offset);
                Type returnType = this.parseSignatureType(mdLoader);
                int sentinelLocation = -1;
                Param[] parameters = new Param[paramCount];
                for (int i = 0; i < paramCount; i++) {
                    byte first = this.buffer[this.offset];
                    if (first == (byte) ElementTypes.SENTINEL) {
                        sentinelLocation = i;
                        this.offset++;
                    }
                    parameters[i] = this.parseSignatureParam(mdLoader);
                }
                SignatureMethod signature =
                    new SignatureMethod(callingConvention, 0, returnType,
                                        parameters, sentinelLocation);
                return new Type(elementType, signature);
            }
            case ElementTypes.VAR:
            case ElementTypes.MVAR: {
                // Generic type variables
                uint number = uncompressInt(this.buffer, ref this.offset);
                return new Type(elementType, number);
            }
            case ElementTypes.GENERICINST: {
                // Generic type instantiation
                Type type = this.parseSignatureType(mdLoader);
                uint typeCount = uncompressInt(this.buffer, ref this.offset);
                Type[] typeParams = new Type[typeCount];
                for (int i = 0; i < typeCount; i++) {
                    Type paramType = this.parseSignatureType(mdLoader);
                    typeParams[i] = paramType;
                }

                return new Type(elementType, type, typeParams);
            }
            case ElementTypes.CMOD_OPT:
            case ElementTypes.CMOD_REQD: {
                // Modifiers
                this.offset--;
                Modifier modifierList = this.parseSignatureModifiers(mdLoader);
                Type type = this.parseSignatureType(mdLoader);
                return new Type(elementType, type, modifierList);
            }
            case ElementTypes.PINNED:
            case ElementTypes.PTR:
            case ElementTypes.BYREF: {
                // Modifiers
                Type type = this.parseSignatureType(mdLoader);
                return new Type(elementType, type, (Modifier) null);
            }
            default: {
                throw new MetaDataLoader.IllegalMetaDataFormatException("Unknown signature type: 0x"+((byte) elementType).ToString("x2")+" at "+this.offset+" in "+this);
            }
          }
      }

      private Modifier parseSignatureModifiers(MetaDataLoader mdLoader) {
          Modifier result = null;
          ElementTypes mod = (ElementTypes) this.buffer[this.offset];
          while (mod == ElementTypes.CMOD_REQD ||
                 mod == ElementTypes.CMOD_OPT) {
              this.offset++;
              uint typeEncoded = uncompressInt(this.buffer, ref this.offset);
              // BUGBUG: type conversion on int.
              MetaDataObject type = mdLoader.getTypeDefOrRef((int) typeEncoded);
              result = new Modifier(mod, type, result);
              if (this.offset < this.buffer.Length) {
                mod = (ElementTypes) this.buffer[this.offset];
              }
              else {
                mod = ElementTypes.VOID;
              }
          }
          return result;
      }

      private Param parseSignatureParam(MetaDataLoader mdLoader) {
          Modifier modifierList = this.parseSignatureModifiers(mdLoader);
          byte first = this.buffer[this.offset];
          if (first == (byte) ElementTypes.BYREF) {
              this.offset++;
              Type type = this.parseSignatureType(mdLoader);
              return new Param(modifierList, (ElementTypes) first, type);
          }
          else if (first == (byte) ElementTypes.TYPEDBYREF) {
              this.offset++;
              return new Param(modifierList, (ElementTypes) first, null);
          }
          else {
              Type type = this.parseSignatureType(mdLoader);
              return new Param(modifierList, ElementTypes.END, type);
          }
      }

      private Type parseSignatureLocal(MetaDataLoader mdLoader) {
          ElementTypes first = (ElementTypes) this.buffer[this.offset];
          if (first == ElementTypes.PINNED) {
              this.offset++;
              Type type = this.parseSignatureType(mdLoader);
              return new Type(first, type, (Modifier) null);
          }
          else {
              return this.parseSignatureType(mdLoader);
          }
      }

      // Debug Methods

      public override string ToString() {
          StringBuilder sb = new StringBuilder("SignatureBuffer(");
          int bufferSize = this.buffer.Length;
          if (bufferSize > 0) {
              sb.Append("0x");
              sb.Append(this.buffer[0].ToString("x2"));
              for (int i = 1; i < bufferSize; i++) {
                  sb.Append(",");
                  sb.Append("0x");
                  sb.Append(this.buffer[i].ToString("x2"));
              }
          }
          sb.Append(")");
          return sb.ToString();
      }

      // State

      private readonly byte[] buffer;
      private int offset;

  }

}
