///////////////////////////////////////////////////////////////////////////////
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
//  Microsoft Research Singularity
//

using System;
using System.Collections;
using System.Diagnostics;

using Microsoft.Singularity.Hal.Acpi.AcpiObject;
using Microsoft.Singularity.Hal.Acpi.AmlParserUnions;
using Node = Microsoft.Singularity.Hal.Acpi.AcpiNamespace.Node;
using NodePath = Microsoft.Singularity.Hal.Acpi.AcpiNamespace.NodePath;
using AbsoluteNodePath = Microsoft.Singularity.Hal.Acpi.AcpiNamespace.AbsoluteNodePath;

namespace Microsoft.Singularity.Hal.Acpi
{
    public class AmlTypeException : Exception
    {
        public AmlTypeException() : base("AML type error") { }

        public AmlTypeException(string s) : base("AML type error: " + s) { }
    }

    public class LoadException : Exception
    {
        public LoadException() : base("Error loading AML") { }

        public LoadException(string s) : base("Error loading AML: " + s) { }
    }

    public class AmlLoader
    {
        AcpiNamespace acpiNamespace;
        AcpiObject.IOperationRegionAccessor operationRegionAccessor;

        public AmlLoader(AcpiNamespace acpiNamespace,
                         AcpiObject.IOperationRegionAccessor operationRegionAccessor)
        {
            this.acpiNamespace = acpiNamespace;
            this.operationRegionAccessor = operationRegionAccessor;
        }

        public void Load(AmlParser.AMLCode code)
        {
            // Because of arbitrary forward-references to names in the AML, we
            // have to do this in three phases:
            // 1. Populate the namespace with all the names;
            // 2. Fill in the details of all the object values.
            // This allows us to verify that references only reference real
            // existing names.

            NamesVisitor namesVisitor = new NamesVisitor(acpiNamespace);
            foreach (TermObj termObj in code.termList)
            {
                termObj.Accept(namesVisitor);
            }

            ValuesVisitor valuesVisitor = new ValuesVisitor(this, acpiNamespace);
            foreach (TermObj termObj in code.termList)
            {
                termObj.Accept(valuesVisitor);
            }
        }

        internal AcpiObject.IOperationRegionAccessor OperationRegionAccessor
        {
            get
            {
                return operationRegionAccessor;
            }
        }

        public class NamesVisitor : AmlParserNodeVisitor
        {
            AcpiNamespace acpiNamespace;
            AbsoluteNodePath currentPath;

            public NamesVisitor(AcpiNamespace acpiNamespace)
            {
                this.acpiNamespace = acpiNamespace;
                this.currentPath = AbsoluteNodePath.CreateRoot();
            }

            public override void UnhandledNodeType(string nodeTypeName)
            {
                throw new LoadException("Encountered unexpected node type " +
                                        nodeTypeName + " at load-time (names phase)");
            }

            public override void Visit(AmlParser.DefAlias defAlias)
            {
                acpiNamespace.CreateNodeAt(defAlias.aliasName.nodePath, currentPath);
            }

            public override void Visit(AmlParser.DefName defName)
            {
                acpiNamespace.CreateNodeAt(defName.nameString.nodePath, currentPath);
            }

            public override void Visit(AmlParser.DefScope defScope)
            {
                AbsoluteNodePath oldPath = currentPath;
                currentPath = acpiNamespace.LookupNode(defScope.nameString.nodePath, currentPath).Path;
                foreach (TermObj termObj in defScope.termList)
                {
                    termObj.Accept(this);
                }
                currentPath = oldPath;
            }

            public override void Visit(AmlParser.DefBankField defBankField)
            {
                foreach (FieldElement fieldElement in defBankField.fieldList) {
                    switch (fieldElement.Tag) {
                        case FieldElement.TagValue.NamedField:
                            AmlParser.NamedField namedField = fieldElement.GetAsNamedField();
                            Node node = acpiNamespace.CreateNodeAt(
                                new NodePath(false/*isAbsolute*/, 0, new string[] { namedField.nameSeg.data }),
                                currentPath);
                            break;
                        default:
                            break;
                    }
                }
            }

            public override void Visit(AmlParser.DefCreateBitField defCreateBitField)
            {
                acpiNamespace.CreateNodeAt(defCreateBitField.nameString.nodePath, currentPath);
            }

            public override void Visit(AmlParser.DefCreateByteField defCreateByteField)
            {
                acpiNamespace.CreateNodeAt(defCreateByteField.nameString.nodePath, currentPath);
            }

            public override void Visit(AmlParser.DefCreateDWordField defCreateDWordField)
            {
                acpiNamespace.CreateNodeAt(defCreateDWordField.nameString.nodePath, currentPath);
            }

            public override void Visit(AmlParser.DefCreateField defCreateField)
            {
                acpiNamespace.CreateNodeAt(defCreateField.nameString.nodePath, currentPath);
            }

            public override void Visit(AmlParser.DefCreateQWordField defCreateQWordField)
            {
                acpiNamespace.CreateNodeAt(defCreateQWordField.nameString.nodePath, currentPath);
            }

            public override void Visit(AmlParser.DefCreateWordField defCreateWordField)
            {
                acpiNamespace.CreateNodeAt(defCreateWordField.nameString.nodePath, currentPath);
            }

            public override void Visit(AmlParser.DefDataRegion defDataRegion)
            {
                acpiNamespace.CreateNodeAt(defDataRegion.nameString.nodePath, currentPath);
            }

            public override void Visit(AmlParser.DefDevice defDevice)
            {
                AbsoluteNodePath oldPath = currentPath;

                Node node = acpiNamespace.CreateNodeAt(defDevice.nameString.nodePath, currentPath);

                currentPath = node.Path;
                foreach (AmlObject amlObject in defDevice.amlObjectList)
                {
                    amlObject.Accept(this);
                }

                currentPath = oldPath;
            }

            public override void Visit(AmlParser.DefEvent defEvent)
            {
                acpiNamespace.CreateNodeAt(defEvent.nameString.nodePath, currentPath);
            }

            public override void Visit(AmlParser.DefField defField)
            {
                foreach (FieldElement fieldElement in defField.fieldList) {
                    switch (fieldElement.Tag) {
                        case FieldElement.TagValue.NamedField:
                            AmlParser.NamedField namedField = fieldElement.GetAsNamedField();
                            Node node = acpiNamespace.CreateNodeAt(
                                new NodePath(false/*isAbsolute*/, 0, new string[] { namedField.nameSeg.data }),
                                currentPath);
                            break;
                        default:
                            break;
                    }
                }
            }

            public override void Visit(AmlParser.DefIndexField defIndexField)
            {
                foreach (FieldElement fieldElement in defIndexField.fieldList) {
                    switch (fieldElement.Tag) {
                        case FieldElement.TagValue.NamedField:
                            AmlParser.NamedField namedField = fieldElement.GetAsNamedField();
                            Node node = acpiNamespace.CreateNodeAt(
                                new NodePath(false/*isAbsolute*/, 0, new string[] { namedField.nameSeg.data }),
                                currentPath);
                            break;
                        default:
                            break;
                    }
                }
            }

            public override void Visit(AmlParser.DefMethod defMethod)
            {
                acpiNamespace.CreateNodeAt(defMethod.nameString.nodePath, currentPath);
            }

            public override void Visit(AmlParser.DefMutex defMutex)
            {
                acpiNamespace.CreateNodeAt(defMutex.nameString.nodePath, currentPath);
            }

            public override void Visit(AmlParser.DefOpRegion defOpRegion)
            {
                acpiNamespace.CreateNodeAt(defOpRegion.nameString.nodePath, currentPath);
            }

            public override void Visit(AmlParser.DefPowerRes defPowerRes)
            {
                AbsoluteNodePath oldPath = currentPath;

                Node node = acpiNamespace.CreateNodeAt(defPowerRes.nameString.nodePath, currentPath);

                currentPath = node.Path;
                foreach (AmlObject amlObject in defPowerRes.amlObjectList)
                {
                    amlObject.Accept(this);
                }

                currentPath = oldPath;
            }

            public override void Visit(AmlParser.DefProcessor defProcessor)
            {
                AbsoluteNodePath oldPath = currentPath;

                Node node = acpiNamespace.CreateNodeAt(defProcessor.nameString.nodePath, currentPath);

                currentPath = node.Path;
                foreach (AmlObject amlObject in defProcessor.amlObjectList)
                {
                    amlObject.Accept(this);
                }

                currentPath = oldPath;
            }

            public override void Visit(AmlParser.DefThermalZone defThermalZone)
            {
                AbsoluteNodePath oldPath = currentPath;

                Node node = acpiNamespace.CreateNodeAt(defThermalZone.nameString.nodePath, currentPath);

                currentPath = node.Path;
                foreach (AmlObject amlObject in defThermalZone.amlObjectList)
                {
                    amlObject.Accept(this);
                }

                currentPath = oldPath;
            }

            public override void Visit(AmlParser.DefIfElse defIfElse)
            {
                //
                // Load-time Ifs are both rare and tricky, because it makes the
                // two-phase model here unworkable: we can't let the NamesVisitor
                // visit the if body before the truth value of its predicate is
                // known, but this may depend on values filled in by the ValuesVisitor.
                // Being an exceptional case, we just have the NamesVisitor always
                // visit both branches, which works for the examples I've come across
                // like the AMD with Infineon TPM.
                //

                foreach (TermObj termObj in defIfElse.termList) {
                    termObj.Accept(this);
                }
                if (defIfElse.defElse.termList != null) {
                    foreach (TermObj termObj in defIfElse.defElse.termList) {
                        termObj.Accept(this);
                    }
                }
            }
        }

        public class ValuesVisitor : AmlParserNodeVisitor
        {
            AcpiNamespace acpiNamespace;
            AmlLoader loader;
            AbsoluteNodePath currentPath;

            public ValuesVisitor(AmlLoader loader, AcpiNamespace acpiNamespace)
            {
                this.acpiNamespace = acpiNamespace;
                this.currentPath = AbsoluteNodePath.CreateRoot();
                this.loader = loader;
            }

            public override void UnhandledNodeType(string nodeTypeName)
            {
                throw new LoadException("Encountered unexpected node type " +
                                        nodeTypeName + " at load-time (values phase)");
            }

            public override void Visit(AmlParser.DefAlias defAlias)
            {
                Node sourceNode = acpiNamespace.LookupNode(defAlias.sourceName.nodePath, currentPath);
                Node aliasNode = acpiNamespace.LookupNode(defAlias.aliasName.nodePath, currentPath);
                aliasNode.AliasTo(sourceNode);
            }

            public override void Visit(AmlParser.DefName defName)
            {
                Node node = acpiNamespace.LookupNode(defName.nameString.nodePath, currentPath);
                node.Value = LoadTimeEvaluate(defName.dataRefObject);
            }

            public override void Visit(AmlParser.DefScope defScope)
            {
                AbsoluteNodePath oldPath = currentPath;
                currentPath = acpiNamespace.LookupNode(defScope.nameString.nodePath, currentPath).Path;
                foreach (TermObj termObj in defScope.termList)
                {
                    termObj.Accept(this);
                }
                currentPath = oldPath;
            }

            public override void Visit(AmlParser.DefBankField defBankField)
            {
                Node operationRegionNode = acpiNamespace.LookupNode(defBankField.regionName.nodePath, currentPath);
                CheckObjectType(operationRegionNode.Value, AcpiObjectType.OperationRegion);

                // TODO: BankFields are not used in the test files and appear to involve some kind of
                // "bank selection register". Need to understand this properly to implement it, but for
                // leaving unimplemented. Commented out below is some code to use as a starting point.

                throw new LoadException("BankField unimplemented");

    #if false

                AccessType accessType = defBankField.fieldFlags.accessType;
                AccessAttrib accessAttrib = AccessAttrib.SMBNone;
                int bitIndex = 0;
                foreach (FieldElement fieldElement in defBankField.fieldList) {
                    switch (fieldElement.Tag) {
                        case FieldElement.TagValue.NamedField:
                            AmlParser.NamedField namedField = fieldElement.GetAsNamedField();
                            Node node = acpiNamespace.LookupNode(
                                new NodePath(false/*isAbsolute*/, 0, new string[] { namedField.nameSeg.data }),
                                currentPath);
                            node.Value = new FieldUnit((AcpiObject.OperationRegion)operationRegionNode.Value,
                                                       bitIndex, namedField.bitWidth,
                                                       accessType, accessAttrib,
                                                       defBankField.fieldFlags.lockRule,
                                                       defBankField.fieldFlags.updateRule);
                            bitIndex += namedField.bitWidth;
                            break;
                        case FieldElement.TagValue.ReservedField:
                            AmlParser.ReservedField reservedField = fieldElement.GetAsReservedField();
                            bitIndex += reservedField.bitWidth;
                            break;
                        case FieldElement.TagValue.AccessField:
                            AmlParser.AccessField accessField = fieldElement.GetAsAccessField();
                            accessType   = accessField.accessType;
                            accessAttrib = accessField.accessAttrib;
                            break;
                        default:
                            throw new LoadException("Unhandled alternative in switch over 'FieldElement'");
                    }
                }
    #endif
            }

            public override void Visit(AmlParser.DefCreateBitField defCreateBitField)
            {
                VisitField(defCreateBitField.sourceBuff,
                           defCreateBitField.bitIndex.integer, 1, 1/*numBits*/,
                           defCreateBitField.nameString.nodePath);
            }

            public override void Visit(AmlParser.DefCreateByteField defCreateByteField)
            {
                VisitField(defCreateByteField.sourceBuff,
                           defCreateByteField.byteIndex.integer, 8, 8/*numBits*/,
                           defCreateByteField.nameString.nodePath);
            }

            public override void Visit(AmlParser.DefCreateDWordField defCreateDWordField)
            {
                VisitField(defCreateDWordField.sourceBuff,
                           defCreateDWordField.byteIndex.integer, 8, 32/*numBits*/,
                           defCreateDWordField.nameString.nodePath);
            }

            public override void Visit(AmlParser.DefCreateField defCreateField)
            {
                AcpiObject.AcpiObject sizeObj = LoadTimeEvaluate(defCreateField.numBits.integer);
                CheckObjectType(sizeObj, AcpiObjectType.Integer);
                VisitField(defCreateField.sourceBuff,
                           defCreateField.bitIndex.integer, 1,
                           ((AcpiObject.Integer)(sizeObj.GetTarget())).Value,
                           defCreateField.nameString.nodePath);
            }

            public override void Visit(AmlParser.DefCreateQWordField defCreateQWordField)
            {
                VisitField(defCreateQWordField.sourceBuff,
                           defCreateQWordField.byteIndex.integer, 8, 64/*numBits*/,
                           defCreateQWordField.nameString.nodePath);
            }

            public override void Visit(AmlParser.DefCreateWordField defCreateWordField)
            {
                VisitField(defCreateWordField.sourceBuff,
                                defCreateWordField.byteIndex.integer, 8, 16/*numBits*/,
                                defCreateWordField.nameString.nodePath);
            }

            public void VisitField(AmlParser.SourceBuff sourceBuff,
                                   TermArg indexTermArg, ulong bitIndexMultiplier,
                                   ulong bitSize,
                                   NodePath fieldName)
            {
                AcpiObject.AcpiObject indexObj = LoadTimeEvaluate(indexTermArg);
                CheckObjectType(indexObj, AcpiObjectType.Integer);

                ulong index = ((AcpiObject.Integer)(indexObj.GetTarget())).Value;
                ulong bitIndex = index * bitIndexMultiplier;

                AcpiObject.AcpiObject bufferObj = LoadTimeEvaluate(sourceBuff.buffer);
                CheckObjectType(bufferObj, AcpiObjectType.Buffer);

                Node node = acpiNamespace.LookupNode(fieldName, currentPath);
                node.Value = new BufferField((AcpiObject.Buffer)(bufferObj.GetTarget()), bitIndex, bitSize);
            }

            public override void Visit(AmlParser.DefDataRegion defDataRegion)
            {
                // TODO: This method will have to go back to the XSDT table
                // to look up the designated table and its location so that
                // it can produce a corresponding AcpiObject.OperationRegion.
                // It is not used in the three test DDBs.
                throw new LoadException("TODO Not yet implemented");
            }

            public override void Visit(AmlParser.DefDevice defDevice)
            {
                AbsoluteNodePath oldPath = currentPath;

                Node node = acpiNamespace.LookupNode(defDevice.nameString.nodePath, currentPath);

                string[] segments = new string[currentPath.NameSegments.Length
                                               + defDevice.nameString.nodePath.NameSegments.Length];

                int index = 0;

                foreach (string segment in currentPath.NameSegments)
                {
                    segments[index++] = segment;
                }

                foreach (string segment in defDevice.nameString.nodePath.NameSegments)
                {
                    segments[index++] = segment;
                }
                
                AbsoluteNodePath devPath = new AbsoluteNodePath(segments);

                node.Value = new AcpiObject.Device(devPath);

                currentPath = node.Path;
                foreach (AmlObject amlObject in defDevice.amlObjectList)
                {
                    amlObject.Accept(this);
                }

                currentPath = oldPath;
            }

            public override void Visit(AmlParser.DefEvent defEvent)
            {
                Node node = acpiNamespace.LookupNode(defEvent.nameString.nodePath, currentPath);
                node.Value = new AcpiObject.Event();
            }

            public override void Visit(AmlParser.DefField defField)
            {
                Node operationRegionNode = acpiNamespace.LookupNode(defField.nameString.nodePath, currentPath);
                CheckObjectType(operationRegionNode.Value, AcpiObjectType.OperationRegion);
                SortedList fields = FieldUnit.CreateFromFieldList((AcpiObject.OperationRegion)(operationRegionNode.Value.GetTarget()),
                                                                  defField.fieldList,
                                                                  defField.fieldFlags.accessType, AccessAttrib.SMBNone,
                                                                  defField.fieldFlags.lockRule, defField.fieldFlags.updateRule);
                foreach (DictionaryEntry entry in fields) {
                    Node node = acpiNamespace.LookupNode(
                        new NodePath(false/*isAbsolute*/, 0, new string[] { (string)entry.Key }),
                        currentPath);
                    node.Value = (FieldUnit)entry.Value;
                }
            }

            public override void Visit(AmlParser.DefIndexField defIndexField)
            {
                Node indexNode = acpiNamespace.LookupNode(defIndexField.indexName.nodePath, currentPath);
                CheckObjectType(indexNode.Value, AcpiObjectType.FieldUnit);
                AcpiObject.FieldUnit indexField = (AcpiObject.FieldUnit)(indexNode.Value.GetTarget());

                Node dataNode = acpiNamespace.LookupNode(defIndexField.dataName.nodePath, currentPath);
                CheckObjectType(dataNode.Value, AcpiObjectType.FieldUnit);
                AcpiObject.FieldUnit dataField = (AcpiObject.FieldUnit)(dataNode.Value.GetTarget());

                OperationRegion indexFieldRegion =
                    new OperationRegion(new IndexFieldOperationRegionAccessor(indexField, dataField),
                                        RegionSpace.SystemIO/*unused*/, 0, 256/*index field never exceeds 8 bits*/);

                AccessType accessType = defIndexField.fieldFlags.accessType;
                AccessAttrib accessAttrib = AccessAttrib.SMBNone;
                int bitIndex = 0;
                foreach (FieldElement fieldElement in defIndexField.fieldList) {
                    switch (fieldElement.Tag) {
                        case FieldElement.TagValue.NamedField:
                            AmlParser.NamedField namedField = fieldElement.GetAsNamedField();
                            Node node = acpiNamespace.LookupNode(
                                new NodePath(false/*isAbsolute*/, 0, new string[] { namedField.nameSeg.data }),
                                currentPath);
                            node.Value = new FieldUnit(indexFieldRegion, bitIndex, namedField.bitWidth,
                                                       accessType, accessAttrib,
                                                       defIndexField.fieldFlags.lockRule,
                                                       defIndexField.fieldFlags.updateRule);
                            bitIndex += namedField.bitWidth;
                            break;
                        case FieldElement.TagValue.ReservedField:
                            AmlParser.ReservedField reservedField = fieldElement.GetAsReservedField();
                            bitIndex += reservedField.bitWidth;
                            break;
                        case FieldElement.TagValue.AccessField:
                            AmlParser.AccessField accessField = fieldElement.GetAsAccessField();
                            accessType   = accessField.accessType;
                            accessAttrib = accessField.accessAttrib;
                            break;
                        default:
                            throw new LoadException("Unhandled alternative in switch over 'FieldElement'");
                    }
                }
            }

            public override void Visit(AmlParser.DefMethod defMethod)
            {
                Node node = acpiNamespace.LookupNode(defMethod.nameString.nodePath, currentPath);
                node.Value = new AcpiObject.BytecodeMethod(defMethod.methodFlags.argCount,
                                                           defMethod.methodFlags.serializeFlag,
                                                           defMethod.methodFlags.syncLevel,
                                                           defMethod.unparsedTermList);
            }

            public override void Visit(AmlParser.DefMutex defMutex)
            {
                Node node = acpiNamespace.LookupNode(defMutex.nameString.nodePath, currentPath);
                node.Value = new AcpiObject.Mutex(defMutex.syncFlags.syncLevel);
            }

            public override void Visit(AmlParser.DefOpRegion defOpRegion)
            {
                AcpiObject.AcpiObject startIndexObj = LoadTimeEvaluate(defOpRegion.regionOffset.integer);
                AcpiObject.AcpiObject lengthObj = LoadTimeEvaluate(defOpRegion.regionLen.integer);
                CheckObjectType(lengthObj, AcpiObjectType.Integer);

                Node node = acpiNamespace.LookupNode(defOpRegion.nameString.nodePath, currentPath);
                node.Value = new AcpiObject.OperationRegion(loader.OperationRegionAccessor,
                                                            (RegionSpace)defOpRegion.regionSpace.byteData,
                                                            startIndexObj.GetAsInt().Value,
                                                            ((AcpiObject.Integer)(lengthObj.GetTarget())).Value);
            }

            public override void Visit(AmlParser.DefPowerRes defPowerRes)
            {
                AbsoluteNodePath oldPath = currentPath;

                Node node = acpiNamespace.LookupNode(defPowerRes.nameString.nodePath, currentPath);
                node.Value = new AcpiObject.PowerResource(defPowerRes.systemLevel.byteData,
                                                          defPowerRes.resourceOrder.wordData);

                currentPath = node.Path;
                foreach (AmlObject amlObject in defPowerRes.amlObjectList)
                {
                    amlObject.Accept(this);
                }

                currentPath = oldPath;
            }

            public override void Visit(AmlParser.DefProcessor defProcessor)
            {
                AbsoluteNodePath oldPath = currentPath;

                Node node = acpiNamespace.LookupNode(defProcessor.nameString.nodePath, currentPath);
                node.Value = new AcpiObject.Processor(defProcessor.procID.byteData,
                                                      defProcessor.pblkAddr.dWordData,
                                                      defProcessor.pblkLen.byteData);

                currentPath = node.Path;
                foreach (AmlObject amlObject in defProcessor.amlObjectList)
                {
                    amlObject.Accept(this);
                }

                currentPath = oldPath;
            }

            public override void Visit(AmlParser.DefThermalZone defThermalZone)
            {
                AbsoluteNodePath oldPath = currentPath;

                Node node = acpiNamespace.LookupNode(defThermalZone.nameString.nodePath, currentPath);
                node.Value = new AcpiObject.ThermalZone();

                currentPath = node.Path;
                foreach (AmlObject amlObject in defThermalZone.amlObjectList)
                {
                    amlObject.Accept(this);
                }

                currentPath = oldPath;
            }

            private AcpiObject.AcpiObject LoadTimeEvaluate(AmlParserNode parserNode)
            {
                LoadTimeEvaluateVisitor visitor =
                    new LoadTimeEvaluateVisitor(acpiNamespace, currentPath);
                parserNode.Accept(visitor);
                return visitor.Result;
            }

            public override void Visit(AmlParser.DefIfElse defIfElse)
            {
                LoadTimeEvaluateVisitor visitor =
                    new LoadTimeEvaluateVisitor(acpiNamespace, currentPath);
                defIfElse.predicate.integer.Accept(visitor);
                if (visitor.Result.GetAsInt().Value != 0) {
                    foreach (TermObj termObj in defIfElse.termList) {
                        termObj.Accept(this);
                    }
                }
                else if (defIfElse.defElse.termList != null) {
                    foreach (TermObj termObj in defIfElse.defElse.termList) {
                        termObj.Accept(this);
                    }
                }
            }
        }

        public class LoadTimeEvaluateVisitor : AmlParserNodeVisitor
        {
            AcpiNamespace acpiNamespace;
            AbsoluteNodePath currentPath;

            public LoadTimeEvaluateVisitor(AcpiNamespace acpiNamespace, AbsoluteNodePath currentPath)
            {
                this.acpiNamespace = acpiNamespace;
                this.currentPath = currentPath;
            }

            public override void UnhandledNodeType(string nodeTypeName)
            {
                throw new LoadException("Encountered unexpected node type " +
                                        nodeTypeName + " at load-time (during evaluation)");
            }

            private AcpiObject.AcpiObject result;

            public AcpiObject.AcpiObject Result
            {
                get
                {
                    return result;
                }
            }

            public override void Visit(AmlParser.DefPackage defPackage)
            {
                VisitPackage(defPackage.numElements.byteData,
                             defPackage.packageElementList);
            }

            public override void Visit(AmlParser.DefVarPackage defVarPackage)
            {
                defVarPackage.varNumElements.integer.Accept(this);
                AcpiObject.AcpiObject numElementsObj = result;
                CheckObjectType(numElementsObj, AcpiObjectType.Integer);
                VisitPackage((byte)(((AcpiObject.Integer)(numElementsObj.GetTarget())).Value),
                             defVarPackage.packageElementList);
            }

            private void VisitPackage(byte numElements, PackageElement[] packageElementList)
            {
                AcpiObjectCell[] elements = new AcpiObjectCell[numElements];
                for(int i = 0; i < elements.Length; i++) {
                    if (i < packageElementList.Length) {
                        packageElementList[i].Accept(this);
                        elements[i] = new AcpiObjectCell(result);
                    }
                    else {
                        elements[i] = new AcpiObjectCell(new AcpiObject.UninitializedObject());
                    }
                }
                result = new AcpiObject.Package(elements);
            }

            public override void Visit(ComputationalData computationalData)
            {
                switch (computationalData.Tag) {
                    case ComputationalData.TagValue.ByteConst:
                        result = new AcpiObject.Integer(computationalData.GetAsByteConst());
                        break;
                    case ComputationalData.TagValue.WordConst:
                        result = new AcpiObject.Integer(computationalData.GetAsWordConst());
                        break;
                    case ComputationalData.TagValue.DWordConst:
                        result = new AcpiObject.Integer(computationalData.GetAsDWordConst());
                        break;
                    case ComputationalData.TagValue.QWordConst:
                        result = new AcpiObject.Integer(computationalData.GetAsQWordConst());
                        break;
                    case ComputationalData.TagValue.StringConst:
                        result = new AcpiObject.String(computationalData.GetAsStringConst());
                        break;
                    case ComputationalData.TagValue.RevisionOp:
                        result = AcpiObject.IntegerConstant.Revision.GetAsInt();
                        break;
                    default:
                        base.Visit(computationalData);
                        break;
                }
            }

            public override void Visit(AmlParser.ConstObj constObj)
            {
                if (constObj.op == AmlParser.ZeroOp) {
                    result = AcpiObject.IntegerConstant.Zero.GetAsInt();
                }
                else if (constObj.op == AmlParser.OneOp) {
                    result = AcpiObject.IntegerConstant.One.GetAsInt();
                }
                else if (constObj.op == AmlParser.OnesOp) {
                    result = AcpiObject.IntegerConstant.Ones.GetAsInt();
                }
            }

            public override void Visit(AmlParser.DefBuffer defBuffer)
            {
                defBuffer.bufferSize.integer.Accept(this);
                AcpiObject.AcpiObject bufferSizeObj = result;
                CheckObjectType(bufferSizeObj, AcpiObjectType.Integer);

                byte[] contents = new byte[((AcpiObject.Integer)(bufferSizeObj.GetTarget())).Value];
                Array.Copy(defBuffer.byteList, contents, defBuffer.byteList.Length);
                result = new AcpiObject.Buffer(contents);
            }

            public override void Visit(AmlParser.UserTermObj userTermObj)
            {
                // At load time, it can't have any args, so just look it up in the namespace.
                // Note that we can't simply copy the value from the given node, for two reasons:
                //
                // 1. UserTermObj references can be forwards or backwards, or even circular, as shown
                //    in this example:
                //            Name (BAR0, Package (0x1) { BAR1 })
                //            Name (BAR1, Package (0x1) { BAR0 })
                // 2. Although the spec doesn't clarify this, I believe a UserTermObj is intended to be
                //    aliased to the named node so that later changes to it are reflected in the object
                //    containing the reference.
                //
                // To deal with we have a special "fake" object type containing an absolute NodePath that
                // acts as a direct reference to an object (not the sort handled by AcpiObject.ObjectReference,
                // which are different). An alternative would be to attempt to use the same aliasing of nodes
                // used by DefAlias, but this would be painful and make it later indistinguishable who is the
                // alias and who the original definition, which might be important.

                result = new AcpiObject.NodePathReference(acpiNamespace,
                             acpiNamespace.LookupNode(userTermObj.nameString.nodePath, currentPath).Path);
            }

            public override void Visit(AmlParser.ObjReference objReference)
            {
                objReference.termArg.Accept(this);
            }
        }

        private static void CheckObjectType(AcpiObject.AcpiObject obj, AcpiObjectType type)
        {
            if (obj.ObjectType().Value != (ulong)type) {
                throw new AmlTypeException();
            }
        }
    }
}
