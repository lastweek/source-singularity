//
// Copyright (c) Microsoft Corporation.   All rights reserved.
//

// Holder of MetaData information

///////////////////////////////////////////////////////////////////////
// 
// The Bartok.msil.MetaData* classes (except MetaDataLoader and
// MetaData) represent entries in the big table of meta data stored
// away in URT binaries.  Each class represents data from one kind of
// entry in the table.  Some of the information in other classes may
// have been incorporated into the representatives (e.g., the
// MetaDataMethod objects have lists of fields and methods).
// 
// The MetaData objects contain the arrays of MetaData* objects
// representing the metadata from a single URT binary.
//
// The MetaDataLoader class is used to load meta data information from
// binaries.  A consumer of meta data information need not inspect
// MetaDataLoader.cs.
// 
//////////////////////////////////////////////////////////////////////  

using System;

namespace Bartok.MSIL
{

  public class MetaData {

      // Constructor Methods

      public static MetaData loadMetaData(String name,
                                          PELoader peLoader) {
          return MetaDataLoader.getMetaData(name, peLoader, false, false);
      }

      public static MetaData loadMetaData(String name,
                                          PELoader peLoader,
                                          bool fLoadCode) {
          return MetaDataLoader.getMetaData(name, peLoader, fLoadCode, false);
      }

      public static MetaData loadMetaData(String name,
                                          PELoader peLoader,
                                          bool fLoadCode,
                                          bool fLoadDebugInfo) {
          return MetaDataLoader.getMetaData(name, peLoader, fLoadCode, fLoadDebugInfo);
      }

      // CLR Profiler seems to blow up when a function has this many
      // parameters.  A fix is to change the fields to internal and set them
      // from MetaDataLoader (the only place to "new MetaData"), but I think
      // that is an unreasonable permanent change just to support that tool.
      internal MetaData(String name,
                        MetaDataMethod entryPoint,
                        int imageBase,
                        MetaDataModule[] moduleArray,
                        MetaDataTypeReference[] typeRefArray,
                        MetaDataTypeDefinition[] typeDefArray,
                        MetaDataFieldPtr[] fieldPtrArray,
                        MetaDataField[] fieldArray,
                        MetaDataMethodPtr[] methodPtrArray,
                        MetaDataMethod[] methodArray,
                        MetaDataParamPtr[] paramPtrArray,
                        MetaDataParam[] paramArray,
                        MetaDataInterfaceImpl[] interfaceImplArray,
                        MetaDataMemberRef[] memberRefArray,
                        MetaDataConstant[] constantArray,
                        MetaDataCustomAttribute[] customAttributeArray,
                        MetaDataFieldMarshal[] fieldMarshalArray,
                        MetaDataDeclSecurity[] declSecurityArray,
                        MetaDataClassLayout[] classLayoutArray,
                        MetaDataFieldLayout[] fieldLayoutArray,
                        MetaDataStandAloneSig[] standAloneSigArray,
                        MetaDataEventMap[] eventMapArray,
                        MetaDataEventPtr[] eventPtrArray,
                        MetaDataEvent[] eventArray,
                        MetaDataPropertyMap[] propertyMapArray,
                        MetaDataPropertyPtr[] propertyPtrArray,
                        MetaDataProperty[] propertyArray,
                        MetaDataMethodSemantics[] methodSemanticsArray,
                        MetaDataMethodImpl[] methodImplArray,
                        MetaDataModuleRef[] moduleRefArray,
                        MetaDataTypeSpec[] typeSpecArray,
                        MetaDataImplMap[] implMapArray,
                        MetaDataFieldRVA[] fieldRVAArray,
                        MetaDataAssembly[] assemblyArray,
                        MetaDataAssemblyProcessor[] assemblyProcessorArray,
                        MetaDataAssemblyOS[] assemblyOSArray,
                        MetaDataAssemblyRef[] assemblyRefArray,
                        MetaDataAssemblyRefProcessor[] assemblyRefProcessorArray,
                        MetaDataAssemblyRefOS[] assemblyRefOSArray,
                        MetaDataFile[] fileArray,
                        MetaDataExportedType[] exportedTypeArray,
                        MetaDataManifestResource[] manifestResourceArray,
                        MetaDataNestedClass[] nestedClassArray,
                        Object[] relocations,
                        MetaDataVtableFixup[] vtableFixupArray,
                        MetaDataDelayImportTable delayImportTable) {
          this.name = name;
          this.entryPoint = entryPoint;
          this.imageBase = imageBase;
          this.moduleArray = moduleArray;
          this.typeRefArray = typeRefArray;
          this.typeDefArray = typeDefArray;
          this.fieldPtrArray = fieldPtrArray;
          this.fieldArray = fieldArray;
          this.methodPtrArray = methodPtrArray;
          this.methodArray = methodArray;
          this.paramPtrArray = paramPtrArray;
          this.paramArray = paramArray;
          this.interfaceImplArray = interfaceImplArray;
          this.memberRefArray = memberRefArray;
          this.constantArray = constantArray;
          this.customAttributeArray = customAttributeArray;
          this.fieldMarshalArray = fieldMarshalArray;
          this.declSecurityArray = declSecurityArray;
          this.classLayoutArray = classLayoutArray;
          this.fieldLayoutArray = fieldLayoutArray;
          this.standAloneSigArray = standAloneSigArray;
          this.eventMapArray = eventMapArray;
          this.eventPtrArray = eventPtrArray;
          this.eventArray = eventArray;
          this.propertyMapArray = propertyMapArray;
          this.propertyPtrArray = propertyPtrArray;
          this.propertyArray = propertyArray;
          this.methodSemanticsArray = methodSemanticsArray;
          this.methodImplArray = methodImplArray;
          this.moduleRefArray = moduleRefArray;
          this.typeSpecArray = typeSpecArray;
          this.implMapArray = implMapArray;
          this.fieldRVAArray = fieldRVAArray;
          this.assemblyArray = assemblyArray;
          this.assemblyProcessorArray = assemblyProcessorArray;
          this.assemblyOSArray = assemblyOSArray;
          this.assemblyRefArray = assemblyRefArray;
          this.assemblyRefProcessorArray = assemblyRefProcessorArray;
          this.assemblyRefOSArray = assemblyRefOSArray;
          this.fileArray = fileArray;
          this.exportedTypeArray = exportedTypeArray;
          this.manifestResourceArray = manifestResourceArray;
          this.nestedClassArray = nestedClassArray;
          this.relocations = relocations;
          this.vtableFixupArray = vtableFixupArray;
          this.delayImportTable = delayImportTable;
          foreach (MetaDataTypeDefinition typeDef in typeDefArray) {
              typeDef.resolveReferences(this);
          }
      }

      // Access Methods

      public void checkOwnership() {
          // BUGBUG
      }

      public string Name {
          get {
              return this.name;
          }
      }

      public MetaDataMethod EntryPoint {
          get {
              return this.entryPoint;
          }
      }

      public int ImageBase {
          get {
              return this.imageBase;
          }
      }

      public MetaDataModule[] Modules {
          get {
              return this.moduleArray;
          }
      }

      public MetaDataTypeReference[] TypeRefs {
          get {
              return this.typeRefArray;
          }
      }

      public MetaDataTypeDefinition[] TypeDefs {
          get {
              return this.typeDefArray;
          }
      }

      public MetaDataFieldPtr[] FieldPtrs {
          get {
              return this.fieldPtrArray;
          }
      }

      public MetaDataField[] Fields {
          get {
              return this.fieldArray;
          }
      }

      public MetaDataMethodPtr[] MethodPtrs {
          get {
              return this.methodPtrArray;
          }
      }

      public MetaDataMethod[] Methods {
          get {
              return this.methodArray;
          }
      }

      public MetaDataParamPtr[] ParamPtrs {
          get {
              return this.paramPtrArray;
          }
      }

      public MetaDataParam[] Parameters {
          get {
              return this.paramArray;
          }
      }

      public MetaDataInterfaceImpl[] InterfaceImpls {
          get {
              return this.interfaceImplArray;
          }
      }

      public MetaDataMemberRef[] MemberRefs {
          get {
              return this.memberRefArray;
          }
      }

      public MetaDataConstant[] Constants {
          get {
              return this.constantArray;
          }
      }

      public MetaDataCustomAttribute[] CustomAttributes {
          get {
              return this.customAttributeArray;
          }
      }

      public MetaDataFieldMarshal[] FieldMarshals {
          get {
              return this.fieldMarshalArray;
          }
      }

      public MetaDataDeclSecurity[] DeclSecurities {
          get {
              return this.declSecurityArray;
          }
      }

      public MetaDataClassLayout[] ClassLayouts {
          get {
              return this.classLayoutArray;
          }
      }

      public MetaDataFieldLayout[] FieldLayouts {
          get {
              return this.fieldLayoutArray;
          }
      }

      public MetaDataStandAloneSig[] StandAloneSigs {
          get {
              return this.standAloneSigArray;
          }
      }

      public MetaDataEventMap[] EventMaps {
          get {
              return this.eventMapArray;
          }
      }

      public MetaDataEventPtr[] EventPtrs {
          get {
              return this.eventPtrArray;
          }
      }

      public MetaDataEvent[] Events {
          get {
              return this.eventArray;
          }
      }

      public MetaDataPropertyMap[] PropertyMaps {
          get {
              return this.propertyMapArray;
          }
      }

      public MetaDataPropertyPtr[] PropertyPtrs {
          get {
              return this.propertyPtrArray;
          }
      }

      public MetaDataProperty[] Properties {
          get {
              return this.propertyArray;
          }
      }

      public MetaDataMethodSemantics[] MethodSemanticss {
          get {
              return this.methodSemanticsArray;
          }
      }

      public MetaDataMethodImpl[] MethodImpls {
          get {
              return this.methodImplArray;
          }
      }

      public MetaDataModuleRef[] ModuleRefs {
          get {
              return this.moduleRefArray;
          }
      }

      public MetaDataTypeSpec[] TypeSpecs {
          get {
              return this.typeSpecArray;
          }
      }

      public MetaDataImplMap[] ImplMaps {
          get {
              return this.implMapArray;
          }
      }

      public MetaDataFieldRVA[] FieldRVAs {
          get {
              return this.fieldRVAArray;
          }
      }

      public MetaDataAssembly[] Assemblies {
          get {
              return this.assemblyArray;
          }
      }

      public MetaDataAssemblyProcessor[] AssemblyProcessors {
          get {
              return this.assemblyProcessorArray;
          }
      }

      public MetaDataAssemblyOS[] AssemblyOSs {
          get {
              return this.assemblyOSArray;
          }
      }

      public MetaDataAssemblyRef[] AssemblyRefs {
          get {
              return this.assemblyRefArray;
          }
      }

      public MetaDataAssemblyRefProcessor[] AssemblyRefProcessors {
          get {
              return this.assemblyRefProcessorArray;
          }
      }

      public MetaDataAssemblyRefOS[] AssemblyRefOSs {
          get {
              return this.assemblyRefOSArray;
          }
      }

      public MetaDataFile[] files {
          get {
              return this.fileArray;
          }
      }

      public MetaDataExportedType[] ExportedTypes {
          get {
              return this.exportedTypeArray;
          }
      }

      public MetaDataManifestResource[] ManifestResources {
          get {
              return this.manifestResourceArray;
          }
      }

      public MetaDataNestedClass[] NestedClasses {
          get {
              return this.nestedClassArray;
          }
      }
      
      public Object[] Relocations {
          get {
              return this.relocations;
          }
      }

      public MetaDataVtableFixup[] VtableFixups {
          get {
              return this.vtableFixupArray;
          }
      }

      public MetaDataDelayImportTable DelayImportTable {
          get {
              return this.delayImportTable;
          }
      }

      public override String ToString() {
          return "MetaData("+this.name+")";
      }

      // State

      private readonly String name;
      private readonly MetaDataMethod entryPoint;
      private readonly int imageBase;
      private readonly MetaDataModule[] moduleArray;
      private readonly MetaDataTypeReference[] typeRefArray;
      private readonly MetaDataTypeDefinition[] typeDefArray;
      private readonly MetaDataFieldPtr[] fieldPtrArray;
      private readonly MetaDataField[] fieldArray;
      private readonly MetaDataMethodPtr[] methodPtrArray;
      private readonly MetaDataMethod[] methodArray;
      private readonly MetaDataParamPtr[] paramPtrArray;
      private readonly MetaDataParam[] paramArray;
      private readonly MetaDataInterfaceImpl[] interfaceImplArray;
      private readonly MetaDataMemberRef[] memberRefArray;
      private readonly MetaDataConstant[] constantArray;
      private readonly MetaDataCustomAttribute[] customAttributeArray;
      private readonly MetaDataFieldMarshal[] fieldMarshalArray;
      private readonly MetaDataDeclSecurity[] declSecurityArray;
      private readonly MetaDataClassLayout[] classLayoutArray;
      private readonly MetaDataFieldLayout[] fieldLayoutArray;
      private readonly MetaDataStandAloneSig[] standAloneSigArray;
      private readonly MetaDataEventMap[] eventMapArray;
      private readonly MetaDataEventPtr[] eventPtrArray;
      private readonly MetaDataEvent[] eventArray;
      private readonly MetaDataPropertyMap[] propertyMapArray;
      private readonly MetaDataPropertyPtr[] propertyPtrArray;
      private readonly MetaDataProperty[] propertyArray;
      private readonly MetaDataMethodSemantics[] methodSemanticsArray;
      private readonly MetaDataMethodImpl[] methodImplArray;
      private readonly MetaDataModuleRef[] moduleRefArray;
      private readonly MetaDataTypeSpec[] typeSpecArray;
      private readonly MetaDataImplMap[] implMapArray;
      private readonly MetaDataFieldRVA[] fieldRVAArray;
      private readonly MetaDataAssembly[] assemblyArray;
      private readonly MetaDataAssemblyProcessor[] assemblyProcessorArray;
      private readonly MetaDataAssemblyOS[] assemblyOSArray;
      private readonly MetaDataAssemblyRef[] assemblyRefArray;
      private readonly MetaDataAssemblyRefProcessor[] assemblyRefProcessorArray;
      private readonly MetaDataAssemblyRefOS[] assemblyRefOSArray;
      private readonly MetaDataFile[] fileArray;
      private readonly MetaDataExportedType[] exportedTypeArray;
      private readonly MetaDataManifestResource[] manifestResourceArray;
      private readonly MetaDataNestedClass[] nestedClassArray;
      private readonly Object[] relocations;
      private readonly MetaDataVtableFixup[] vtableFixupArray;
      private readonly MetaDataDelayImportTable delayImportTable;

  }

}
