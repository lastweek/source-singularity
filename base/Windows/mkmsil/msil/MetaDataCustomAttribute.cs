// 
// Copyright (c) Microsoft Corporation.   All rights reserved.
//

using System;

namespace Bartok.MSIL
{

  using System.IO;

  public class MetaDataCustomAttribute: MetaDataObject {

      // Constructor Methods

      internal MetaDataCustomAttribute(int parentIndex,
                                       MetaDataObject type,
                                       byte[] buffer) {
          this.parentIndex = parentIndex;
          this.type = type;
          this.buffer = buffer;
      }

      // This is technically not a constructor method, but it is meant to
      // be used to set up the object
      internal void resolveReferences(MetaDataLoader loader) {
          this.parent = loader.getHasCustomAttribute(this.parentIndex);
          this.parent.AddCustomAttribute(this);
      }

      // Resolve all the custom attributes found in the assemblies registered
      // in 'resolver', using all the type information found in 'resolver' and
      // 'resolvers'.
      internal void resolveReferences(MetaDataResolver resolver,
                                      MetaDataResolver[] resolvers)
      {
          if (this.buffer[0] != 0x01 || this.buffer[1] != 0x00) {
              throw new MetaDataLoader.IllegalMetaDataFormatException("Custom Attribute doesn't start with 0x0001!");
          }
          SignatureMethod signature;
          if (this.type is MetaDataMethod) {
              MetaDataMethod method = (MetaDataMethod) this.type;
              signature = (SignatureMethod) method.Signature;
              if (!method.Name.Equals(".ctor")) {
                  throw new MetaDataLoader.IllegalMetaDataFormatException("Custom attribute with unexpected method name: "+method.Name);
              }
              this.typeDefOrRef = method.Parent;
              this.name = method.Parent.FullName;
          }
          else if (this.type is MetaDataMemberRef) {
              MetaDataMemberRef memberRef = (MetaDataMemberRef) this.type;
              signature = (SignatureMethod) memberRef.Signature;
              if (!memberRef.Name.Equals(".ctor")) {
                  throw new MetaDataLoader.IllegalMetaDataFormatException("Custom attribute with unexpected memberRef name: "+memberRef.Name);
              }
              MetaDataObject methodParent = memberRef.Class;
              this.typeDefOrRef = methodParent;
              if (methodParent is MetaDataTypeDefinition) {
                  this.name = ((MetaDataTypeDefinition) methodParent).FullName;
              }
              else if (methodParent is MetaDataTypeReference) {
                  this.name = ((MetaDataTypeReference) methodParent).FullName;
              }
              else {
                  throw new MetaDataLoader.IllegalMetaDataFormatException("Custom attribute with unexpected class type: "+methodParent);
              }
          }
          else {
              throw new MetaDataLoader.IllegalMetaDataFormatException("Custom attribute with unexpected type: "+this.type);
          }
          Signature.Param[] parameters = signature.Parameters;
          int fixedCount = parameters.Length;
          this.fixedArgs = new Object[fixedCount];
          MemoryStream stream =
              new MemoryStream(this.buffer, 2, this.buffer.Length - 2, false);
          BinaryReader reader = new BinaryReader(stream);
          for (int i = 0; i < fixedCount; i++) {
              Signature.Param parameter = parameters[i];
              Signature.Type paramType = parameter.Type;
              Object value =
                  ExtractParameter(paramType, reader, resolver, resolvers);
              fixedArgs[i] = value;
          }
          short namedCount = ((reader.PeekChar() == -1) ?
                              (short) 0 :
                              reader.ReadInt16());
          if (namedCount > this.buffer.Length &&
              this.Name.Equals("System.Runtime.CompilerServices.RequiredAttributeAttribute")) {
              // Some CLR libraries have been compiled against a version of
              // mscorlib that had a fixed parameter to RequiredAttribute.
              // Simply ignore whatever the parameter was!
              namedCount = 0;
          }
          this.namedArgs = new NamedArg[namedCount];
          for (int i = 0; i < namedCount; i++) {
              SerializationTypes propOrField = (SerializationTypes)
                  reader.ReadByte();
              ElementTypes fieldType = (ElementTypes) reader.ReadByte();
              ElementTypes arrayType = ElementTypes.END;
              switch (fieldType) {
                case ElementTypes.SZARRAY: {
                    arrayType = (ElementTypes) reader.ReadByte();
                    if (arrayType == (ElementTypes) SerializationTypes.ENUM) {
                        throw new Exception("Not implemented: Array of ENUM "+
                                            "for named field/property");
                    }
                    break;
                }
                case (ElementTypes) SerializationTypes.ENUM: {
                    String enumName = ExtractString(reader);
                    if (enumName.Length == 0) {
                        throw new Exception("Empty enum name");
                    }
                    // Hope it is a 4-byte enum
                    fieldType = (ElementTypes) SerializationTypes.U4;
                    break;
                }
                case (ElementTypes) SerializationTypes.TAGGED_OBJECT: {
                    throw new Exception("Not implemented: "+fieldType+
                                        " for named field/property");
                }
                default: {
                    break;
                }
              }
              String name = ExtractString(reader);
              Object value;
              if (fieldType == ElementTypes.SZARRAY) {
                  value = ExtractArrayValue(arrayType, reader);
              }
              else {
                  value = ExtractValue(fieldType, reader);
              }
              if (propOrField == SerializationTypes.FIELD ||
                  propOrField == SerializationTypes.PROPERTY) {
                  this.namedArgs[i] =
                      new NamedArg(propOrField == SerializationTypes.FIELD,
                                   -1, name, value);
              }
              else {
                  throw new MetaDataLoader.IllegalMetaDataFormatException("Unknown prop-or-field type: "+propOrField);
              }
          }
      }

      private static MetaDataObject ResolveTypeRef(MetaDataResolver resolver,
                                                   MetaDataResolver[] resolvers,
                                                   MetaDataTypeReference typeRef) {
          MetaDataObject result = resolver.ResolveTypeRef(typeRef);
          int i = 0;
          while (result == null && i < resolvers.Length) {
              MetaDataResolver testResolver = resolvers[i];
              i++;
              if (testResolver != resolver) {
                  result = testResolver.ResolveTypeRef(typeRef);
              }
          }
          return result;
      }

      private static MetaDataTypeDefinition ResolveName(MetaDataResolver resolver,
                                                        MetaDataResolver[] resolvers,
                                                        String typeName) {
          MetaDataTypeDefinition typeDef = resolver.ResolveName(typeName);
          int i = 0;
          while (typeDef == null && i < resolvers.Length) {
              MetaDataResolver testResolver = resolvers[i];
              i++;
              if (testResolver != resolver) {
                  typeDef = testResolver.ResolveName(typeName);
              }
          }
          return typeDef;
      }

      private static Object ExtractParameter(Signature.Type type,
                                             BinaryReader reader,
                                             MetaDataResolver resolver,
                                             MetaDataResolver[] resolvers)
      {
          switch (type.ElementType) {
            case ElementTypes.VALUETYPE: {
                MetaDataObject classObject = type.ClassObject;
                if (classObject is MetaDataTypeReference) {
                    MetaDataTypeReference classReference =
                        (MetaDataTypeReference) classObject;
                    MetaDataObject resolvedObject =
                        ResolveTypeRef(resolver, resolvers, classReference);
                    if (resolvedObject is MetaDataTypeDefinition) {
                        classObject = resolvedObject;
                    }
                }
                if (classObject is MetaDataTypeReference) {
                    // We will simply assume it is an I4 enum
                    Console.Out.WriteLine("====>>> WARNING: Making I4 enum assumption for "+classObject);
                    return reader.ReadInt32();
                }
                else if (classObject is MetaDataTypeDefinition) {
                    MetaDataTypeDefinition classDef =
                        (MetaDataTypeDefinition) classObject;
                    MetaDataObject superClass = classDef.Extends;
                    String superName;
                    if (superClass is MetaDataTypeDefinition) {
                        superName =
                            ((MetaDataTypeDefinition) superClass).FullName;
                    }
                    else if (superClass is MetaDataTypeReference) {
                        superName =
                            ((MetaDataTypeReference) superClass).FullName;
                    }
                    else {
                        throw new MetaDataLoader.IllegalMetaDataFormatException("Unexpected superclass of valuetype: "+superClass);
                    }
                    if (!superName.Equals("System.Enum")) {
                        throw new MetaDataLoader.IllegalMetaDataFormatException("Found valuetype that wasn't an Enum");
                    }
                    return ExtractEnumValue(classDef, reader,
                                            resolver, resolvers);
                }
                else {
                    throw new MetaDataLoader.IllegalMetaDataFormatException("Unexpected valuetype class: "+classObject);
                }
            }
            case ElementTypes.CLASS: {
                MetaDataObject classObject = type.ClassObject;
                if (classObject is MetaDataTypeReference) {
                    MetaDataTypeReference classReference =
                        (MetaDataTypeReference) classObject;
                    MetaDataObject resolvedObject =
                        ResolveTypeRef(resolver, resolvers, classReference);
                    if (resolvedObject is MetaDataTypeDefinition) {
                        classObject = resolvedObject;
                    }
                }
                String className;
                if (classObject is MetaDataTypeReference) {
                    className =
                        ((MetaDataTypeReference) classObject).FullName;
                }
                else if (classObject is MetaDataTypeDefinition) {
                    className =
                        ((MetaDataTypeDefinition) classObject).FullName;
                }
                else {
                    throw new MetaDataLoader.IllegalMetaDataFormatException("Unexpected class: "+classObject);
                }
                if (className.Equals("System.String")) {
                    return ExtractString(reader);
                }
                else if (className.Equals("System.Object")) {
                    goto case ElementTypes.OBJECT;
                }
                else if (className.Equals("System.Type")) {
                    return ExtractString(reader);
                }
                if (!(classObject is MetaDataTypeDefinition)) {
                    throw new MetaDataLoader.IllegalMetaDataFormatException("Cannot determine whether the following is an array: "+classObject);
                }
                MetaDataObject superClass =
                    ((MetaDataTypeDefinition) classObject).Extends;
                Console.WriteLine("class is "+classObject);
                throw new Exception("Not implemented: object encoding an array");
            }
            case ElementTypes.OBJECT:
            case (ElementTypes) SerializationTypes.TAGGED_OBJECT: {
                SerializationTypes objectType = (SerializationTypes)
                    reader.ReadByte();
                switch (objectType) {
                  case SerializationTypes.ENUM: {
                      String typeName = ExtractString(reader);
                      // Some Stringified type names include a bunch of 
                      // information past the type, none of which we
                      // are concerned about for the moment.
                      int nameEnd = typeName.IndexOf(',');
                      if (nameEnd >= 0) {
                          typeName = typeName.Substring(0, nameEnd);
                      }
                      // A type defined within another type has a "+"
                      // as the separator.  Convert it to ".", which is
                      // the convention the rest of the reader uses.
                      typeName = typeName.Replace('+','.');
                      MetaDataTypeDefinition typeDef =
                          ResolveName(resolver, resolvers, typeName);
                      if (typeDef == null) {
                          throw new Exception("No typedef for "+typeName);
                      }
                      return ExtractEnumValue(typeDef, reader,
                                              resolver, resolvers);
                  }
                  case SerializationTypes.TYPE: {
                      return ExtractValue((ElementTypes) objectType,
                                          reader);
                  }
                  default: {
                      throw new Exception("Found OBJECT type with type "+objectType);
                  }
                }
            }
            case ElementTypes.SZARRAY: {
                return ExtractArrayValue(type.TypeObject, reader,
                                         resolver, resolvers);
            }
            default: {
                return ExtractValue(type.ElementType, reader);
            }
          }
      }

      private static Object ExtractValue(ElementTypes type,
                                         BinaryReader reader)
      {
          switch (type) {
            case ElementTypes.BOOLEAN:
                return reader.ReadBoolean();
            case ElementTypes.CHAR:
                return (char) reader.ReadUInt16();
            case ElementTypes.I1:
                return reader.ReadSByte();
            case ElementTypes.U1:
                return reader.ReadByte();
            case ElementTypes.I2:
                return reader.ReadInt16();
            case ElementTypes.U2:
                return reader.ReadUInt16();
            case ElementTypes.I4:
                return reader.ReadInt32();
            case ElementTypes.U4:
                return reader.ReadUInt32();
            case ElementTypes.I8:
                return reader.ReadInt64();
            case ElementTypes.U8:
                return reader.ReadUInt64();
            case ElementTypes.R4:
                return reader.ReadSingle();
            case ElementTypes.R8:
                return reader.ReadDouble();
            case ElementTypes.STRING:
            case (ElementTypes) SerializationTypes.TYPE:
                return ExtractString(reader); 
            default:
                throw new MetaDataLoader.IllegalMetaDataFormatException("Found unexpected type "+type+" in custom attribute parameter");
          }
      }

      private static String ExtractString(BinaryReader reader) {
          byte firstByte = reader.ReadByte();
          if (firstByte == 0xFF) {
              return null;
          }
          int size;
          if ((firstByte & 0x80) == 0) {
              // encoded in a single byte
              size = firstByte;
          }
          else if ((firstByte & 0x40) == 0) {
              // encoded in two bytes
              size = unchecked(((firstByte & 0x3F) << 8) |
                               reader.ReadByte());
          }
          else {
              // encoded in four bytes
              size = unchecked((int) (((firstByte & 0x3F) << 24) |
                                      (reader.ReadByte() << 16) |
                                      (reader.ReadByte() << 8) |
                                      (reader.ReadByte())));
          }
          byte[] bytes = reader.ReadBytes(size);
          if (bytes.Length != size) {
              throw new Exception("Didn't get the bytes requested");
          }
          return (new System.Text.UTF8Encoding()).GetString(bytes);
      }

      private static Object ExtractEnumValue(MetaDataTypeDefinition typeDef,
                                             BinaryReader reader,
                                             MetaDataResolver resolver,
                                             MetaDataResolver[] resolvers)
      {
          MetaDataField[] classFields = typeDef.Fields;
          for (int i = 0; i < classFields.Length; i++) {
              if ((classFields[i].Flags & (int) MetaDataField.FieldAttributes.Static) == 0) {
                  if (!classFields[i].Name.Equals("value__")) {
                      throw new MetaDataLoader.IllegalMetaDataFormatException("Found enum with non-static field "+classFields[i].Name);
                  }
                  return ExtractParameter(classFields[i].Signature.FieldType,
                                          reader, resolver, resolvers);
              }
          }
          throw new MetaDataLoader.IllegalMetaDataFormatException("Found enum without non-static field");
      }

      private static Object ExtractArrayValue(Signature.Type type,
                                              BinaryReader reader,
                                              MetaDataResolver resolver,
                                              MetaDataResolver[] resolvers)
      {
          int arraySize = reader.ReadInt32();
          if (arraySize >= 0) {
              ElementTypes elementType = type.ElementType;
              if (elementType == ElementTypes.CLASS) {
                  Object[] array = new Object[arraySize];
                  for (int i = 0; i < arraySize; i++) {
                      array[i] = ExtractParameter(type, reader,
                                                  resolver, resolvers);
                  }
                  return array;
              }
              else {
                  return ExtractArrayValue(elementType, arraySize, reader);
              }
          }
          else {
              throw new Exception("Not implemented: custom attribute class "+
                                  "array with negative length");
          }
      }

      
      private static Object ExtractArrayValue(ElementTypes elementType,
                                              BinaryReader reader)
      {
          int arraySize = reader.ReadInt32();
          if (arraySize >= 0) {
              return ExtractArrayValue(elementType, arraySize, reader);
          }
          else {
              throw new Exception("Not implemented: custom atribute array "+
                                  "with negative length");
          }
      }
              

      private static Object ExtractArrayValue(ElementTypes elementType,
                                              int arraySize,
                                              BinaryReader reader)
      {
          switch (elementType) {
            case ElementTypes.BOOLEAN: {
                bool[] array = new bool[arraySize];
                for (int i = 0; i < arraySize; i++) {
                    array[i] = reader.ReadBoolean();
                }
                return array;
            }
            case ElementTypes.CHAR: {
                char[] array = new char[arraySize];
                for (int i = 0; i < arraySize; i++) {
                    array[i] = (char) reader.ReadUInt16();
                }
                return array;
            }
            case ElementTypes.I1: {
                sbyte[] array = new sbyte[arraySize];
                for (int i = 0; i < arraySize; i++) {
                    array[i] = reader.ReadSByte();
                }
                return array;
            }
            case ElementTypes.U1: {
                byte[] array = new byte[arraySize];
                for (int i = 0; i < arraySize; i++) {
                    array[i] = reader.ReadByte();
                }
                return array;
            }
            case ElementTypes.I2: {
                short[] array = new short[arraySize];
                for (int i = 0; i < arraySize; i++) {
                    array[i] = reader.ReadInt16();
                }
                return array;
            }
            case ElementTypes.U2: {
                ushort[] array = new ushort[arraySize];
                for (int i = 0; i < arraySize; i++) {
                    array[i] = reader.ReadUInt16();
                }
                return array;
            }
            case ElementTypes.I4: {
                int[] array = new int[arraySize];
                for (int i = 0; i < arraySize; i++) {
                    array[i] = reader.ReadInt32();
                }
                return array;
            }
            case ElementTypes.U4: {
                uint[] array = new uint[arraySize];
                for (int i = 0; i < arraySize; i++) {
                    array[i] = reader.ReadUInt32();
                }
                return array;
            }
            case ElementTypes.I8: {
                long[] array = new long[arraySize];
                for (int i = 0; i < arraySize; i++) {
                    array[i] = reader.ReadInt64();
                }
                return array;
            }
            case ElementTypes.U8: {
                ulong[] array = new ulong[arraySize];
                for (int i = 0; i < arraySize; i++) {
                    array[i] = reader.ReadUInt64();
                }
                return array;
            }
            case ElementTypes.R4: {
                float[] array = new float[arraySize];
                for (int i = 0; i < arraySize; i++) {
                    array[i] = reader.ReadSingle();
                }
                return array;
            }
            case ElementTypes.R8: {
                double[] array = new double[arraySize];
                for (int i = 0; i < arraySize; i++) {
                    array[i] = reader.ReadDouble();
                }
                return array;
            }
            case ElementTypes.STRING: {
                String[] array = new String[arraySize];
                for (int i = 0; i < arraySize; i++) {
                    array[i] = ExtractString(reader);
                }
                return array;
            }
            default:
                throw new Exception("Not implemented: custom attribute "+
                                    "array of type "+elementType);
          }
      }

      // Access Methods

      // Who owns this custom attribute
      public MetaDataObject Parent {
          get { return this.parent; }
      }

      // The fully qualified name of the custom attribute
      public String Name {
          get { return this.name; }
      }

      // The type definition or reference of the custom attribute
      public MetaDataObject TypeDefOrRef {
          get { return this.typeDefOrRef; }
      }

      // The constructor method or memberref of the custom attribute
      public MetaDataObject Type {
          get { return this.type; }
      }

      // The array of arguments to the custom attribute constructor
      public Object[] FixedArgs {
          get { return this.fixedArgs; }
      }

      // The array of custom attribute fields and properties explicitly set
      public NamedArg[] NamedArgs {
          get { return this.namedArgs; }
      }

      // Debug Methods

      public override String ToString() {
          return ("MetaDataCustomAttribute("+
                  this.type+","+this.fixedArgs+","+this.namedArgs+","+
                  this.parentIndex+
                  (this.parent==null?"":("<"+this.parent.ToString()+">"))+
                  ")["+new MetaDataBlob(this.buffer)+"]");
      }

      public override String ToStringLong() {
          System.Text.StringBuilder sb =
              new System.Text.StringBuilder("MetaDataCustomAttribute(");
          sb.Append(this.type);
          sb.Append(",");
          if (this.fixedArgs != null) {
              sb.Append("FixedArgs(");
              for (int i = 0; i < this.fixedArgs.Length; i++) {
                  sb.Append(this.fixedArgs[i]);
                  sb.Append(",");
              }
              sb.Append("),");
          }
          else {
              sb.Append("FixedArgs(),");
          }
          if (this.namedArgs != null) {
              sb.Append("NamedArgs(");
              for (int i = 0; i < this.namedArgs.Length; i++) {
                  sb.Append(this.namedArgs[i]);
                  sb.Append(",");
              }
              sb.Append("),");
          }
          else {
              sb.Append("NamedArgs(),");
          }
          sb.Append(this.parent);
          sb.Append("(");
          sb.Append(this.parentIndex);
          sb.Append("))[");
          sb.Append(new MetaDataBlob(this.buffer));
          sb.Append("]");
          return sb.ToString();
      }

      // State

      private readonly byte[]         buffer;
      private readonly int            parentIndex;
      private          String         name;
      private          MetaDataObject parent;
      private          MetaDataObject type;
      private          MetaDataObject typeDefOrRef;
      private          Object[]       fixedArgs;
      private          NamedArg[]     namedArgs;

      public class FixedArg {

          // A negative value for arrayDim signifies a nonArray
          internal FixedArg(SerializationTypes type, int arrayDim,
                            Object value) {
              this.arrayDim = arrayDim;
              this.type = type;
              this.value = value;
          }

          public bool IsArray {
              get { return this.arrayDim >= 0; }
          }

          public int ArrayDim {
              get {
                  if (this.arrayDim < 0) {
                      throw new Exception("FixedArg is not an array");
                  }
                  return this.arrayDim;
              }
          }

          public SerializationTypes Type {
              get { return this.type; }
          }

          public Object Value {
              get { return this.value; }
          }

          public override String ToString() {
              return ("FixedArg("+this.type+((arrayDim<0)?"":("["+arrayDim+"]"))+"->"+this.value+")");
          }

          private int arrayDim;
          private SerializationTypes type;
          private Object value;

      }

      public class NamedArg {

          internal NamedArg(bool isFieldArg,  int arrayDim,
                            String name, Object value)
          {
              this.isFieldArg = isFieldArg;
              this.arrayDim = arrayDim;
              this.type = type;
              this.name = name;
              this.value = value;
          }

          public bool IsFieldArg {
              get { return this.isFieldArg; }
          }

          public bool IsArray {
              get { return this.arrayDim >= 0; }
          }

          public int ArrayDim {
              get {
                  if (this.arrayDim < 0) {
                      throw new Exception("NamedArg is not an array");
                  }
                  return this.arrayDim;
              }
          }

          public SerializationTypes Type {
              get { return this.type; }
          }

          public String Name {
              get { return this.name; }
          }

          public Object Value {
              get { return this.value; }
          }

          public override String ToString() {
              return ("NamedArg("+this.name+":"+this.type+((arrayDim<0)?"":("["+arrayDim+"]"))+"->"+this.value+")");
          }

          private bool isFieldArg;
          private int arrayDim;
          private String name;
          private SerializationTypes type;
          private Object value;

      }

  }

}
