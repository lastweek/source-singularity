#
# Copyright (c) Microsoft Corporation.   All rights reserved.
#

!if "$(ROOT)" == ""
ROOT = ..
!endif

NAMESPACE = Bartok.MSIL

SUB_DIRS =

LIB_FILES = \
    $(SRCDIR)\EHClause.cs \
    $(SRCDIR)\Instruction.cs \
    $(SRCDIR)\MarshalSpec.cs \
    $(SRCDIR)\MetaData.cs \
    $(SRCDIR)\MetaDataAssembly.cs \
    $(SRCDIR)\MetaDataAssemblyOS.cs \
    $(SRCDIR)\MetaDataAssemblyProcessor.cs \
    $(SRCDIR)\MetaDataAssemblyRef.cs \
    $(SRCDIR)\MetaDataAssemblyRefOS.cs \
    $(SRCDIR)\MetaDataAssemblyRefProcessor.cs \
    $(SRCDIR)\MetaDataBits.cs \
    $(SRCDIR)\MetaDataBlob.cs \
    $(SRCDIR)\MetaDataClassLayout.cs \
    $(SRCDIR)\MetaDataConstant.cs \
    $(SRCDIR)\MetaDataCustomAttribute.cs \
    $(SRCDIR)\MetaDataDeclSecurity.cs \
    $(SRCDIR)\MetaDataEvent.cs \
    $(SRCDIR)\MetaDataEventMap.cs \
    $(SRCDIR)\MetaDataEventPtr.cs \
    $(SRCDIR)\MetaDataExportedType.cs \
    $(SRCDIR)\MetaDataField.cs \
    $(SRCDIR)\MetaDataFieldLayout.cs \
    $(SRCDIR)\MetaDataFieldMarshal.cs \
    $(SRCDIR)\MetaDataFieldPtr.cs \
    $(SRCDIR)\MetaDataFieldRVA.cs \
    $(SRCDIR)\MetaDataFile.cs \
    $(SRCDIR)\MetaDataGenericParam.cs \
    $(SRCDIR)\MetaDataGenericParamConstraint.cs \
    $(SRCDIR)\MetaDataImplMap.cs \
    $(SRCDIR)\MetaDataImplSpec.cs \
    $(SRCDIR)\MetaDataInterfaceImpl.cs \
    $(SRCDIR)\MetaDataLoader.cs \
    $(SRCDIR)\MetaDataManifestResource.cs \
    $(SRCDIR)\MetaDataMemberRef.cs \
    $(SRCDIR)\MetaDataMethod.cs \
    $(SRCDIR)\MetaDataMethodImpl.cs \
    $(SRCDIR)\MetaDataMethodPtr.cs \
    $(SRCDIR)\MetaDataMethodSemantics.cs \
    $(SRCDIR)\MetaDataMethodSpec.cs \
    $(SRCDIR)\MetaDataModule.cs \
    $(SRCDIR)\MetaDataModuleRef.cs \
    $(SRCDIR)\MetaDataNestedClass.cs \
    $(SRCDIR)\MetaDataObject.cs \
    $(SRCDIR)\MetaDataParam.cs \
    $(SRCDIR)\MetaDataParamPtr.cs \
    $(SRCDIR)\MetaDataProperty.cs \
    $(SRCDIR)\MetaDataPropertyMap.cs \
    $(SRCDIR)\MetaDataPropertyPtr.cs \
    $(SRCDIR)\MetaDataResolver.cs \
    $(SRCDIR)\MetaDataStandAloneSig.cs \
    $(SRCDIR)\MetaDataTypeDefinition.cs \
    $(SRCDIR)\MetaDataTypeReference.cs \
    $(SRCDIR)\MetaDataTypeSpec.cs \
    $(SRCDIR)\MetaDataVtableFixup.cs \
    $(SRCDIR)\MetaDataDelayImportTable.cs \
    $(SRCDIR)\PDBLoader.cs \
    $(SRCDIR)\PELoader.cs \
    $(SRCDIR)\Signature.cs \
    $(SRCDIR)\SignatureField.cs \
    $(SRCDIR)\SignatureLocalVar.cs \
    $(SRCDIR)\SignatureMethod.cs \
    $(SRCDIR)\SignatureProperty.cs \
    $(SRCDIR)\SignatureTypeSpec.cs \

#LIB_FILES = $(LIB_FILES) \
#   $(SRCDIR)\Disassembler.cs \
#   $(SRCDIR)\Disassembler.exe \

LIB_IMPORTS = \
    Bartok.Datatype.dll \
    Bartok.DebugInfo.dll

LIB_CSCFLAGS =

!include $(ROOT)\build\makefile.library

#Disassembler.exe: *.cs
#   csc /out:Disassembler.exe /debug /define:DEBUG /r:Bartok.Utility.dll;Bartok.Datatype.dll /lib:..\Debug *.cs
