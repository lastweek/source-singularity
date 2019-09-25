//
// Copyright (c) Microsoft Corporation.   All rights reserved.
//

using System;

namespace Bartok.MSIL
{

  using System.Collections;
  using System.Reflection;

  public class MetaDataTypeDefinition: MetaDataObject {

      // Constructor Methods

      internal MetaDataTypeDefinition(TypeAttributes flags, string name,
                                      string nameSpace, int extendsIndex,
                                      int fieldIndex, int methodIndex) {
          this.flags = flags;
          this.name = name;
          this.nameSpace = nameSpace;
          this.extendsIndex = extendsIndex;
          this.fieldIndex = fieldIndex;
          this.methodIndex = methodIndex;
      }

      // These are technically not constructor methods, but they are meant
      // to be used to set up the object

      internal void AddGenericParam(MetaDataGenericParam genericParam) {
          if (this.genericParamList == null) {
              this.genericParamList = new ArrayList(2);
          }

          if (genericParam.Number != this.genericParamList.Count) {
              throw new MetaDataLoader.IllegalMetaDataFormatException
                  ("Generic parameters out of order - is this allowed?");
          }

          this.genericParamList.Add(genericParam);
      }

      internal void registerReferences(int fieldCount, int methodCount,
                                       MetaDataTypeDefinition[] fieldOwners,
                                       MetaDataTypeDefinition[] methodOwners) {
          if (this.fieldIndex <= fieldCount) {
              fieldOwners[this.fieldIndex] = this;
          }
          if (this.methodIndex <= methodCount) {
              methodOwners[this.methodIndex] = this;
          }
      }

      internal void resolveReferences(MetaDataLoader loader,
                                      MetaDataTypeDefinition[] fieldOwners,
                                      MetaDataTypeDefinition[] methodOwners) {
          this.extends = loader.getTypeDefOrRef(this.extendsIndex);
          // fieldOwners[fieldOwners.Length-1] == null, so this is safe
          int fieldEndIndex = this.fieldIndex ;
          while (fieldOwners[fieldEndIndex] == this) {
              loader.getField(fieldEndIndex).resolveReferences(this);
              fieldEndIndex++;
          }
          int fieldCount = fieldEndIndex - this.fieldIndex;
          this.fieldArray = loader.getFields(this.fieldIndex, fieldCount);
          // methodOwners[methodOwners.Length-1] == null, so this is safe
          int methodEndIndex = this.methodIndex;
          while (methodOwners[methodEndIndex] == this) {
              loader.getMethod(methodEndIndex).setParent(this);
              methodEndIndex++;
          }
          int methodCount = methodEndIndex - this.methodIndex;
          this.methodArray = loader.getMethods(this.methodIndex, methodCount);
      }

      internal void resolveReferences(MetaDataTypeDefinition enclosingClass) {
          this.enclosingClass = enclosingClass;
      }

      internal void resolveReferences(MetaDataTypeDefinition[] nestedClasses) {
          this.nestedClasses = nestedClasses;
      }

      internal void resolveReferences(MetaDataClassLayout classLayout) {
          this.classLayout = classLayout;
      }

      internal void resolveReferences(MetaDataObject[] interfaces) {
          this.interfaces = interfaces;
      }

      internal void resolveReferences(MetaData owner) {
          this.owner = owner;
      }

      // Access Methods

      public TypeAttributes Flags {
          get {
              return this.flags;
          }
      }

      public string Name {
          get {
              return this.name;
          }
      }

      public string Namespace {
          get {
              return this.nameSpace;
          }
      }

      // of MetaDataGenericParam
      public ArrayList GenericParamList {
          get {
              return this.genericParamList;
          }
      }

      public MetaDataObject Extends {
          get {
              return this.extends;
          }
      }

      public MetaDataObject[] Interfaces {
          get {
              return this.interfaces;
          }
      }

      public MetaDataField[] Fields {
          get {
              return this.fieldArray;
          }
      }

      public MetaDataMethod[] Methods {
          get {
              return this.methodArray;
          }
      }

      public MetaDataTypeDefinition EnclosingClass {
          get {
              return this.enclosingClass;
          }
      }

      public MetaDataTypeDefinition[] NestedClasses {
          get {
              return this.nestedClasses;
          }
      }

      public MetaDataClassLayout ClassLayout {
          get {
              return this.classLayout;
          }
      }

      // for non-nested types, returns <Namespace>.<Name>
      // for nested types, returns <enclosing class's FullName>.<Name>
      public string FullName {
          get {
              String name;
              if (this.Namespace.Length == 0) {
                  if (this.IsNestedType) {
                      name = this.EnclosingClass.FullName+"."+this.Name;
                  }
                  else {
                      name = this.Name;
                  }
              }
              else {
                  if (this.IsNestedType) {
                      // TODO: verify that we don't need to fail
                      // when this happens:
                      // throw new Exception("Nested type with namespace");
                  }
                  name = this.Namespace+"."+this.Name;
              }
              return name;
          }
      }

      public MetaData Owner {
          get {
              return this.owner;
          }
      }

      public override string ToString() {
          return ("MetaDataTypeDefinition("+this.FullName+")");
      }

      public override string ToStringLong() {
          System.Text.StringBuilder sb =
              new System.Text.StringBuilder("MetaDataTypeDefinition(");
          sb.Append(((int) this.flags).ToString("x")); sb.Append(",");
          sb.Append(this.FullName); sb.Append(",");
          if (this.genericParamList != null
              && this.genericParamList.Count > 0) {
              sb.Append("GenericParams<");
              foreach (MetaDataGenericParam param in this.genericParamList) {
                  sb.Append(param.ToString());
                  sb.Append(",");
              }
              sb.Remove(sb.Length-1, 1);
              sb.Append(">,");
          }
          if (this.extends == null) {
              sb.Append(this.extendsIndex);
          }
          else {
              sb.Append(this.extends.ToString());
              sb.Append("("); sb.Append(this.extendsIndex); sb.Append(")");
          }
          sb.Append(",");
          if (this.interfaces != null && this.interfaces.Length > 0) {
              sb.Append("interfaces(");
              foreach (MetaDataObject interfaceObject in this.interfaces) {
                  sb.Append(interfaceObject.ToString());
                  sb.Append(",");
              }
              sb.Remove(sb.Length-1, 1);
              sb.Append(")");
          }
          else {
              sb.Append("No interfaces");
          }
          sb.Append(",");
          if (this.fieldArray != null && this.methodArray != null) {
              if (this.fieldArray.Length > 0) {
                  sb.Append("fields(");
                  foreach (MetaDataField field in this.fieldArray) {
                      sb.Append(field.ToString());
                      sb.Append(",");
                  }
                  sb.Remove(sb.Length-1, 1);
                  sb.Append(")");
              }
              else {
                  sb.Append("No fields");
              }
              sb.Append(",");
              if (this.methodArray.Length > 0) {
                  sb.Append("methods(");
                  foreach (MetaDataMethod method in this.methodArray) {
                      sb.Append(method.ToString());
                      sb.Append(",");
                  }
                  sb.Remove(sb.Length-1, 1);
                  sb.Append(")");
              }
              else {
                  sb.Append("No methods");
              }
          }
          else {
              sb.Append(this.fieldIndex);
              sb.Append(",");
              sb.Append(this.methodIndex);
          }
          sb.Append(")");
          return sb.ToString();
      }

      // other utilities

      public bool IsNestedType {
          get {
              return enclosingClass != null;
          }
      }

      // State

      private readonly TypeAttributes           flags;
      private readonly string                   name;
      private readonly string                   nameSpace;
      private readonly int                      extendsIndex;
      private          ArrayList                genericParamList;
      private          MetaDataObject           extends;
      private          MetaDataObject[]         interfaces;
      private readonly int                      fieldIndex;
      private          MetaDataField[]          fieldArray;
      private readonly int                      methodIndex;
      private          MetaDataMethod[]         methodArray;
      private          MetaDataTypeDefinition   enclosingClass;
      private          MetaDataTypeDefinition[] nestedClasses;
      private          MetaDataClassLayout      classLayout;
      private          MetaData                 owner;

  }

}
