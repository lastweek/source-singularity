///////////////////////////////////////////////////////////////////////////////
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
//  Microsoft Research Singularity
//

// The AML stack IR is a proprietary linearized representation of an AML method.
// By converting the AML to a linearized IR, we can deal with cooperative
// multithreading more easily, because it's easier to represent and explicitly
// store the current state of the interpreter. This transformation also provides
// an opportunity to eliminate redundancies in the original representation.

using System;
using System.Collections;
using System.Diagnostics;

using Node = Microsoft.Singularity.Hal.Acpi.AcpiNamespace.Node;
using NodePath = Microsoft.Singularity.Hal.Acpi.AcpiNamespace.NodePath;
using AbsoluteNodePath = Microsoft.Singularity.Hal.Acpi.AcpiNamespace.AbsoluteNodePath;

using Microsoft.Singularity.Hal.Acpi.AcpiObject;
using Microsoft.Singularity.Hal.Acpi.StackIR;
using Microsoft.Singularity.Hal.Acpi.AmlParserUnions;

namespace Microsoft.Singularity.Hal.Acpi.StackIR
{
    public abstract class StackIRNode
    {
        public abstract void Accept(StackIRNodeVisitor v);
    }

    public class Jump : StackIRNode
    {
        public override void Accept(StackIRNodeVisitor v)
        {
            v.Visit(this);
        }

        int target;

        public int Target {
            get
            {
                return target;
            }
            set
            {
                target = value;
            }
        }
    }

    public class JumpIfNonZero : StackIRNode
    {
        public override void Accept(StackIRNodeVisitor v)
        {
            v.Visit(this);
        }

        int thenTarget;

        public int ThenTarget {
            get
            {
                return thenTarget;
            }
            set
            {
                thenTarget = value;
            }
        }
    }

    public class PushArgObj : StackIRNode
    {
        int argNum;

        public PushArgObj(int argNum)
        {
            this.argNum = argNum;
        }

        public override void Accept(StackIRNodeVisitor v)
        {
            v.Visit(this);
        }

        public int ArgNum
        {
            get
            {
                return argNum;
            }
        }
    }

    public class PushLocalObj : StackIRNode
    {
        int localNum;

        public PushLocalObj(int localNum)
        {
            this.localNum = localNum;
        }

        public override void Accept(StackIRNodeVisitor v)
        {
            v.Visit(this);
        }

        public int LocalNum
        {
            get
            {
                return localNum;
            }
        }
    }

    public class PushDebugObj : StackIRNode
    {
        public override void Accept(StackIRNodeVisitor v)
        {
            v.Visit(this);
        }
    }

    public class PushNodePath : StackIRNode
    {
        NodePath value;

        public PushNodePath(NodePath value)
        {
            this.value = value;
        }

        public override void Accept(StackIRNodeVisitor v)
        {
            v.Visit(this);
        }

        public NodePath Value
        {
            get
            {
                return value;
            }
        }
    }

    public class PushConst : StackIRNode
    {
        AcpiObject.AcpiObject value;

        public PushConst(AcpiObject.AcpiObject value)
        {
            this.value = value;
        }

        public override void Accept(StackIRNodeVisitor v)
        {
            v.Visit(this);
        }

        public AcpiObject.AcpiObject Value
        {
            get
            {
                return value;
            }
        }
    }

    public class Discard : StackIRNode
    {
        public override void Accept(StackIRNodeVisitor v)
        {
            v.Visit(this);
        }
    }

    // Store a value in a location *and* push it on the stack
    public class Store : StackIRNode
    {
        public override void Accept(StackIRNodeVisitor v)
        {
            v.Visit(this);
        }
    }
    
    public class MethodCall : StackIRNode
    {
        public override void Accept(StackIRNodeVisitor v)
        {
            v.Visit(this);
        }
    }

    public class Index : StackIRNode
    {
        public override void Accept(StackIRNodeVisitor v)
        {
            v.Visit(this);
        }
    }
    
    public class ShiftLeft : StackIRNode
    {
        public override void Accept(StackIRNodeVisitor v)
        {
            v.Visit(this);
        }
    }

    public class ShiftRight : StackIRNode
    {
        public override void Accept(StackIRNodeVisitor v)
        {
            v.Visit(this);
        }
    }

    public class Concatenate : StackIRNode
    {
        public override void Accept(StackIRNodeVisitor v)
        {
            v.Visit(this);
        }
    }

    public class Add : StackIRNode
    {
        public override void Accept(StackIRNodeVisitor v)
        {
            v.Visit(this);
        }
    }

    public class Subtract : StackIRNode
    {
        public override void Accept(StackIRNodeVisitor v)
        {
            v.Visit(this);
        }
    }

    public class Multiply : StackIRNode
    {
        public override void Accept(StackIRNodeVisitor v)
        {
            v.Visit(this);
        }
    }

    public class Divide : StackIRNode
    {
        public override void Accept(StackIRNodeVisitor v)
        {
            v.Visit(this);
        }
    }

    public class Remainder : StackIRNode
    {
        public override void Accept(StackIRNodeVisitor v)
        {
            v.Visit(this);
        }
    }

    public class FindSetLeftBit : StackIRNode
    {
        public override void Accept(StackIRNodeVisitor v)
        {
            v.Visit(this);
        }
    }

    public class FindSetRightBit : StackIRNode
    {
        public override void Accept(StackIRNodeVisitor v)
        {
            v.Visit(this);
        }
    }

    public class SizeOf : StackIRNode
    {
        public override void Accept(StackIRNodeVisitor v)
        {
            v.Visit(this);
        }
    }

    public class LogicalOp : StackIRNode
    {
        public enum Op
        {
            Less,
            LessEq,
            Equal,
            Greater,
            GreaterEq,
            And,
            Or,
            Not
        }

        Op op;

        public LogicalOp(Op op)
        {
            this.op = op;
        }

        public override void Accept(StackIRNodeVisitor v)
        {
            v.Visit(this);
        }

        public Op Operator
        {
            get
            {
                return op;
            }
        }
    }

    public class BitOp : StackIRNode
    {
        public enum Op
        {
            And,
            Or,
            NAnd,
            NOr,
            Not,
            XOr
        }

        Op op;

        public BitOp(Op op)
        {
            this.op = op;
        }

        public override void Accept(StackIRNodeVisitor v)
        {
            v.Visit(this);
        }

        public Op Operator
        {
            get
            {
                return op;
            }
        }
    }

    public class Return : StackIRNode
    {
        public override void Accept(StackIRNodeVisitor v)
        {
            v.Visit(this);
        }
    }
    
    public class CreateField : StackIRNode
    {
        NodePath nodePath;

        public CreateField(NodePath nodePath)
        {
            this.nodePath = nodePath;
        }

        public override void Accept(StackIRNodeVisitor v)
        {
            v.Visit(this);
        }

        public NodePath NodePath
        {
            get
            {
                return nodePath;
            }
        }
    }
    
    public class DefBuffer : StackIRNode
    {
        byte[] initializer;

        public DefBuffer(byte[] initializer)
        {
            this.initializer = initializer;
        }

        public override void Accept(StackIRNodeVisitor v)
        {
            v.Visit(this);
        }

        public byte[] Initializer
        {
            get
            {
                return (byte[])initializer.Clone();
            }
        }
    }
    
    public class DefName : StackIRNode
    {
        NodePath nodePath;

        public DefName(NodePath nodePath)
        {
            this.nodePath = nodePath;
        }

        public override void Accept(StackIRNodeVisitor v)
        {
            v.Visit(this);
        }

        public NodePath NodePath
        {
            get
            {
                return nodePath;
            }
        }
    }

    public class Load : StackIRNode
    {
        NodePath nodePath;

        public Load(NodePath nodePath)
        {
            this.nodePath = nodePath;
        }

        public override void Accept(StackIRNodeVisitor v)
        {
            v.Visit(this);
        }

        public NodePath NodePath
        {
            get
            {
                return nodePath;
            }
        }
    }

    public class Stall : StackIRNode
    {
        public override void Accept(StackIRNodeVisitor v)
        {
            v.Visit(this);
        }
    }

    public class Match : StackIRNode
    {
        AmlParser.MatchOpcode matchOp1, matchOp2;

        public Match(AmlParser.MatchOpcode matchOp1, AmlParser.MatchOpcode matchOp2)
        {
            this.matchOp1 = matchOp1;
            this.matchOp2 = matchOp2;
        }

        public override void Accept(StackIRNodeVisitor v)
        {
            v.Visit(this);
        }
    }
    
    public class DerefOf : StackIRNode
    {
        public override void Accept(StackIRNodeVisitor v)
        {
            v.Visit(this);
        }
    }

    public class Package : StackIRNode
    {
        int numElements;

        public Package(int numElements)
        {
            this.numElements = numElements;
        }

        public override void Accept(StackIRNodeVisitor v)
        {
            v.Visit(this);
        }
    }

    public class Notify : StackIRNode
    {
        public override void Accept(StackIRNodeVisitor v)
        {
            v.Visit(this);
        }
    }

    public class Sleep : StackIRNode
    {
        public override void Accept(StackIRNodeVisitor v)
        {
            v.Visit(this);
        }
    }

    public class RefOf : StackIRNode
    {
        public override void Accept(StackIRNodeVisitor v)
        {
            v.Visit(this);
        }
    }

    public class JumpIfNodePathExists : StackIRNode
    {
        private NodePath nodePath;

        public JumpIfNodePathExists(NodePath nodePath)
        {
            this.nodePath = nodePath;
        }

        public NodePath NodePath
        {
            get
            {
                return nodePath;
            }
        }

        int thenTarget;

        public int ThenTarget {
            get
            {
                return thenTarget;
            }
            set
            {
                thenTarget = value;
            }
        }

        public override void Accept(StackIRNodeVisitor v)
        {
            v.Visit(this);
        }
    }

    public class OperationRegion : StackIRNode
    {
        RegionSpace operationSpace;
        NodePath nodePath;

        public OperationRegion(RegionSpace operationSpace, NodePath nodePath)
        {
            this.operationSpace = operationSpace;
            this.nodePath = nodePath;
        }

        public override void Accept(StackIRNodeVisitor v)
        {
            v.Visit(this);
        }

        public RegionSpace OperationSpace
        {
            get
            {
                return operationSpace;
            }
        }

        public NodePath NodePath
        {
            get
            {
                return nodePath;
            }
        }
    }

    public class Field : StackIRNode
    {
        AmlParser.FieldFlags fieldFlags;
        NodePath nodePath;
        FieldElement[] fieldElements;

        public Field(AmlParser.FieldFlags fieldFlags, NodePath nodePath, FieldElement[] fieldElements)
        {
            this.fieldFlags = fieldFlags;
            this.nodePath = nodePath;
            this.fieldElements = fieldElements;
        }

        public override void Accept(StackIRNodeVisitor v)
        {
            v.Visit(this);
        }

        public AmlParser.FieldFlags FieldFlags
        {
            get
            {
                return fieldFlags;
            }
        }

        public NodePath NodePath
        {
            get
            {
                return nodePath;
            }
        }

        public FieldElement[] FieldElements
        {
            get
            {
                return fieldElements;
            }
        }
    }

    public class Acquire : StackIRNode
    {
        ushort timeout;

        public Acquire(ushort timeout)
        {
            this.timeout = timeout;
        }

        public override void Accept(StackIRNodeVisitor v)
        {
            v.Visit(this);
        }
    }

    public class Release : StackIRNode
    {
        public override void Accept(StackIRNodeVisitor v)
        {
            v.Visit(this);
        }
    }

    public class ToBuffer : StackIRNode
    {
        public override void Accept(StackIRNodeVisitor v)
        {
            v.Visit(this);
        }
    }

    public class ToInteger : StackIRNode
    {
        public override void Accept(StackIRNodeVisitor v)
        {
            v.Visit(this);
        }
    }

    public class ToString : StackIRNode
    {
        public override void Accept(StackIRNodeVisitor v)
        {
            v.Visit(this);
        }
    }

    public abstract class StackIRNodeVisitor
    {
        public abstract void Visit(Jump node);
        public abstract void Visit(JumpIfNonZero node);
        public abstract void Visit(JumpIfNodePathExists node);
        public abstract void Visit(PushArgObj node);
        public abstract void Visit(PushLocalObj node);
        public abstract void Visit(PushDebugObj node);
        public abstract void Visit(PushNodePath node);
        public abstract void Visit(PushConst node);
        public abstract void Visit(Discard node);
        public abstract void Visit(Store node);
        public abstract void Visit(MethodCall node);
        public abstract void Visit(Index node);
        public abstract void Visit(Add node);
        public abstract void Visit(Subtract node);
        public abstract void Visit(Multiply node);
        public abstract void Visit(Divide node);
        public abstract void Visit(Remainder node);
        public abstract void Visit(ShiftLeft node);
        public abstract void Visit(ShiftRight node);
        public abstract void Visit(Concatenate node);
        public abstract void Visit(LogicalOp node);
        public abstract void Visit(BitOp node);
        public abstract void Visit(Return node);
        public abstract void Visit(CreateField node);
        public abstract void Visit(FindSetLeftBit node);
        public abstract void Visit(FindSetRightBit node);
        public abstract void Visit(SizeOf node);
        public abstract void Visit(DefName node);
        public abstract void Visit(Load node);
        public abstract void Visit(Stall node);
        public abstract void Visit(Match node);
        public abstract void Visit(DerefOf node);
        public abstract void Visit(Package node);
        public abstract void Visit(DefBuffer node);
        public abstract void Visit(Notify node);
        public abstract void Visit(Sleep node);
        public abstract void Visit(RefOf node);
        public abstract void Visit(OperationRegion node);
        public abstract void Visit(Field node);
        public abstract void Visit(Acquire node);
        public abstract void Visit(Release node);
        public abstract void Visit(ToBuffer node);
        public abstract void Visit(ToInteger node);
        public abstract void Visit(ToString node);
    }
}

namespace Microsoft.Singularity.Hal.Acpi
{
    public class AmlToStackIRException : Exception
    {
        // TODO
    }

    public class AmlToStackIRVisitor : AmlParserNodeVisitor
    {
        private class StackIRNodeList
        {
            ArrayList list = new ArrayList();

            public void Add(StackIRNode node) {
                list.Add(node);
            }

            public StackIRNode[] ToArray() {
                return (StackIRNode[])list.ToArray(typeof(StackIRNode));
            }

            public StackIRNode Last
            {
                get
                {
                    return (StackIRNode)list[list.Count - 1];
                }
            }

            public int Count
            {
                get
                {
                    return list.Count;
                }
            }
        }

        StackIRNodeList result = new StackIRNodeList();

        public StackIRNode[] Result
        {
            get
            {
                // Tack on a return of an uninitialized object at the end
                // so it doesn't run off the end.
                result.Add(new PushConst(new UninitializedObject()));
                result.Add(new Return());

                return result.ToArray();
            }
        }

        public override void UnhandledNodeType(string nodeTypeName)
        {
            throw new AmlToStackIRException();
        }
        
        public void VisitSequence(AmlParserNode[] nodeSequence)
        {
            if (nodeSequence == null) {
                return;
            }
            foreach (AmlParserNode node in nodeSequence) {
                node.Accept(this);
                DiscardResults();
            }
        }

        public void DiscardResults()
        {
            // Certain operations produce results in contexts where we
            // don't need them. This throws them away if so.
            if (result.Count > 0 && result.Last is Store) {
                result.Add(new Discard());
            }
        }

        public void VisitSequenceReverse(AmlParserNode[] nodeSequence)
        {
            for(int i = nodeSequence.Length - 1; i >= 0; i--) {
                nodeSequence[i].Accept(this);
            }
        }

        public override void Visit(AmlParser.DefIfElse defIfElse)
        {
            // We create a sequence like this:
            // (push predicate)
            // jump if nonzero to thenBranch
            // (else branch instructions)
            // jump to end
            // elseBranch:
            // (then branch instructions)
            // end:

            defIfElse.predicate.Accept(this);
            JumpIfNonZero thenJump = new JumpIfNonZero();
            result.Add(thenJump);
            defIfElse.defElse.Accept(this);
            Jump jumpOverThenBrach = new Jump();
            result.Add(jumpOverThenBrach);
            thenJump.ThenTarget = result.Count;
            VisitSequence(defIfElse.termList);
            jumpOverThenBrach.Target = result.Count;
        }

        public override void Visit(AmlParser.Predicate predicate)
        {
            predicate.integer.Accept(this);
        }

        public override void Visit(AmlParser.DefElse defElse)
        {
            VisitSequence(defElse.termList);
        }

        public override void Visit(AmlParser.ArgObj argObj)
        {
            result.Add(new PushArgObj(argObj.op));
        }

        public override void Visit(AmlParser.LocalObj localObj)
        {
            result.Add(new PushLocalObj(localObj.op));
        }

        public override void Visit(AmlParser.IndexValue indexValue)
        {
            indexValue.integer.Accept(this);
        }

        public override void Visit(AmlParser.ShiftCount shiftCount)
        {
            shiftCount.integer.Accept(this);
        }

        public override void Visit(AmlParser.BuffPkgStrObj buffPkgStrObj)
        {
            buffPkgStrObj.termArg.Accept(this);
        }

        public override void Visit(AmlParser.Target target)
        {
            target.superName.Accept(this);
        }

        public override void Visit(AmlParser.Operand operand)
        {
            operand.integer.Accept(this);
        }

        public override void Visit(AmlParser.ArgObject argObject)
        {
            argObject.dataRefObject.Accept(this);
        }

        public override void Visit(AmlParser.BitIndex bitIndex)
        {
            bitIndex.integer.Accept(this);
        }

        public override void Visit(AmlParser.ByteIndex byteIndex)
        {
            byteIndex.integer.Accept(this);
        }

        public override void Visit(AmlParser.SourceBuff sourceBuff)
        {
            sourceBuff.buffer.Accept(this);
        }

        public override void Visit(AmlParser.StartIndex startIndex)
        {
            startIndex.integer.Accept(this);
        }

        public override void Visit(AmlParser.ObjReference objReference)
        {
            objReference.termArg.Accept(this);
        }

        public override void Visit(AmlParser.SearchPkg searchPkg)
        {
            searchPkg.package.Accept(this);
        }

        public override void Visit(AmlParser.NumBits numBits)
        {
            numBits.integer.Accept(this);
        }

        public override void Visit(AmlParser.NotifyValue notifyValue)
        {
            notifyValue.integer.Accept(this);
        }
        
        public override void Visit(AmlParser.NotifyObject notifyObject)
        {
            notifyObject.superName.Accept(this);
        }

        public override void Visit(AmlParser.MsecTime msecTime)
        {
            msecTime.integer.Accept(this);
        }

        public override void Visit(AmlParser.RegionLen regionLen)
        {
            regionLen.integer.Accept(this);
        }

        public override void Visit(AmlParser.RegionOffset regionOffset)
        {
            regionOffset.integer.Accept(this);
        }

        public override void Visit(AmlParser.MutexObject mutexObject)
        {
            mutexObject.superName.Accept(this);
        }
        
        public override void Visit(AmlParser.LengthArg lengthArg)
        {
            lengthArg.integer.Accept(this);
        }
        
        public override void Visit(AmlParser.DDBHandleObject ddbHandleObject)
        {
            ddbHandleObject.superName.Accept(this);
        }    

        public override void Visit(AmlParser.UsecTime usecTime)
        {
            usecTime.byteData.Accept(this);
        }    

        public override void Visit(AmlParser.Dividend dividend)
        {
            dividend.integer.Accept(this);
        }

        public override void Visit(AmlParser.Divisor divisor)
        {
            divisor.integer.Accept(this);
        }

        public override void Visit(AmlParser.Remainder remainder)
        {
            remainder.target.Accept(this);
        }

        public override void Visit(AmlParser.Quotient quotient)
        {
            quotient.target.Accept(this);
        }

        public override void Visit(AmlParser.Data data)
        {
            data.computationalData.Accept(this);
        }

        public override void Visit(AmlParser.DefStore defStore)
        {
            defStore.superName.Accept(this);
            defStore.termArg.Accept(this);
            result.Add(new Store());
        }

        public override void Visit(AmlParser.NameString nameString)
        {
            result.Add(new PushNodePath(nameString.nodePath));
        }

        public override void Visit(ComputationalData computationalData)
        {
            switch (computationalData.Tag) {
                case ComputationalData.TagValue.ByteConst:
                    byte byteConst = computationalData.GetAsByteConst();
                    result.Add(new PushConst(new AcpiObject.Integer(byteConst)));
                    break;
                case ComputationalData.TagValue.WordConst:
                    UInt16 wordConst = computationalData.GetAsWordConst();
                    result.Add(new PushConst(new AcpiObject.Integer(wordConst)));
                    break;
                case ComputationalData.TagValue.DWordConst:
                    UInt32 dWordConst = computationalData.GetAsDWordConst();
                    result.Add(new PushConst(new AcpiObject.Integer(dWordConst)));
                    break;
                case ComputationalData.TagValue.QWordConst:
                    UInt64 qWordConst = computationalData.GetAsQWordConst();
                    result.Add(new PushConst(new AcpiObject.Integer(qWordConst)));
                    break;
                case ComputationalData.TagValue.StringConst:
                    string stringConst = computationalData.GetAsStringConst();
                    result.Add(new PushConst(new AcpiObject.String(stringConst)));
                    break;
                case ComputationalData.TagValue.ConstObj:
                    AmlParser.ConstObj constObj = computationalData.GetAsConstObj();
                    switch (constObj.op) {
                        case AmlParser.ZeroOp:
                            result.Add(new PushConst(AcpiObject.IntegerConstant.Zero));
                            break;
                        case AmlParser.OneOp:
                            result.Add(new PushConst(AcpiObject.IntegerConstant.One));
                            break;
                        case AmlParser.OnesOp:
                            result.Add(new PushConst(AcpiObject.IntegerConstant.Ones));
                            break;
                    }
                    break;
                case ComputationalData.TagValue.RevisionOp:
                    result.Add(new PushConst(AcpiObject.IntegerConstant.Revision));
                    break;
                case ComputationalData.TagValue.DefBuffer:
                    AmlParser.DefBuffer defBuffer = computationalData.GetAsDefBuffer();
                    defBuffer.Accept(this);
                    break;
                default:
                    Debug.Assert(false, "Unhandled alternative in switch over 'ComputationalData'");
                    break;
            }
        }

        public override void Visit(AmlParser.DefName defName)
        {
            defName.dataRefObject.Accept(this);
            result.Add(new DefName(defName.nameString.nodePath));
        }

        public override void Visit(AmlParser.UserTermObj userTermObj)
        {
            if (userTermObj.termArgList.Length > 0) {
                VisitSequenceReverse(userTermObj.termArgList);
                result.Add(new PushNodePath(userTermObj.nameString.nodePath));
                result.Add(new MethodCall());
            }
            else {
                // The interpreter will determine at runtime if this is a method or not
                result.Add(new PushNodePath(userTermObj.nameString.nodePath));
            }
        }

        public override void Visit(AmlParser.DefCreateField defCreateField)
        {
            defCreateField.numBits.Accept(this);
            defCreateField.bitIndex.Accept(this);
            defCreateField.sourceBuff.Accept(this);
            result.Add(new CreateField(defCreateField.nameString.nodePath));
        }

        public override void Visit(AmlParser.DefCreateBitField defCreateBitField)
        {
            result.Add(new PushConst(new AcpiObject.Integer(1))); // number of bits
            defCreateBitField.bitIndex.Accept(this);
            defCreateBitField.sourceBuff.Accept(this);
            result.Add(new CreateField(defCreateBitField.nameString.nodePath));
        }

        public override void Visit(AmlParser.DefCreateByteField defCreateByteField)
        {
            result.Add(new PushConst(new AcpiObject.Integer(8))); // number of bits

            // Multiply byte index by 8 to get bit index
            defCreateByteField.byteIndex.Accept(this);
            result.Add(new PushConst(new AcpiObject.Integer(8)));
            result.Add(new Multiply());

            defCreateByteField.sourceBuff.Accept(this);
            result.Add(new CreateField(defCreateByteField.nameString.nodePath));
        }

        public override void Visit(AmlParser.DefCreateWordField defCreateWordField)
        {
            result.Add(new PushConst(new AcpiObject.Integer(16))); // number of bits

            // Multiply byte index by 8 to get bit index
            defCreateWordField.byteIndex.Accept(this);
            result.Add(new PushConst(new AcpiObject.Integer(8)));
            result.Add(new Multiply());

            defCreateWordField.sourceBuff.Accept(this);
            result.Add(new CreateField(defCreateWordField.nameString.nodePath));
        }

        public override void Visit(AmlParser.DefCreateDWordField defCreateDWordField)
        {
            result.Add(new PushConst(new AcpiObject.Integer(32))); // number of bits

            // Multiply byte index by 8 to get bit index
            defCreateDWordField.byteIndex.Accept(this);
            result.Add(new PushConst(new AcpiObject.Integer(8)));
            result.Add(new Multiply());

            defCreateDWordField.sourceBuff.Accept(this);
            result.Add(new CreateField(defCreateDWordField.nameString.nodePath));
        }

        public override void Visit(AmlParser.DefCreateQWordField defCreateQWordField)
        {
            result.Add(new PushConst(new AcpiObject.Integer(64))); // number of bits

            // Multiply byte index by 8 to get bit index
            defCreateQWordField.byteIndex.Accept(this);
            result.Add(new PushConst(new AcpiObject.Integer(8)));
            result.Add(new Multiply());

            defCreateQWordField.sourceBuff.Accept(this);
            result.Add(new CreateField(defCreateQWordField.nameString.nodePath));
        }

        public override void Visit(AmlParser.DefBuffer defBuffer)
        {
            defBuffer.bufferSize.integer.Accept(this);
            result.Add(new DefBuffer(defBuffer.byteList));
        }

        public override void Visit(AmlParser.DefDecrement defDecrement)
        {
            defDecrement.superName.Accept(this); // target

            result.Add(new PushConst(new AcpiObject.Integer(1)));
            defDecrement.superName.Accept(this); // left
            result.Add(new Subtract());

            result.Add(new Store());
        }

        public override void Visit(AmlParser.DefIncrement defIncrement)
        {
            defIncrement.superName.Accept(this); // target

            result.Add(new PushConst(new AcpiObject.Integer(1)));
            defIncrement.superName.Accept(this); // left
            result.Add(new Add());

            result.Add(new Store());
        }

        public override void Visit(AmlParser.DefPackage defPackage)
        {
            VisitSequenceReverse(defPackage.packageElementList);
            result.Add(new Microsoft.Singularity.Hal.Acpi.StackIR.Package(
                defPackage.numElements.byteData));
        }

        public override void Visit(AmlParser.DefFindSetLeftBit defFindSetLeftBit)
        {
            VisitUnaryOperator(defFindSetLeftBit.operand, defFindSetLeftBit.target, new FindSetLeftBit());
        }

        public override void Visit(AmlParser.DefFindSetRightBit defFindSetRightBit)
        {
            VisitUnaryOperator(defFindSetRightBit.operand, defFindSetRightBit.target, new FindSetRightBit());
        }

        public override void Visit(AmlParser.DefSizeOf defSizeOf)
        {
            defSizeOf.superName.Accept(this);
            result.Add(new SizeOf());
        }

        public override void Visit(AmlParser.DefIndex defIndex)
        {
            VisitBinaryOperator(defIndex.buffPkgStrObj, defIndex.indexValue, defIndex.target, new Index());
        }

        public override void Visit(AmlParser.DefAdd defAdd)
        {
            VisitBinaryOperator(defAdd.leftOperand, defAdd.rightOperand, defAdd.target, new Add());
        }

        public override void Visit(AmlParser.DefSubtract defSubtract)
        {
            VisitBinaryOperator(defSubtract.leftOperand, defSubtract.rightOperand, defSubtract.target, new Subtract());
        }

        public override void Visit(AmlParser.DefMultiply defMultiply)
        {
            VisitBinaryOperator(defMultiply.leftOperand, defMultiply.rightOperand, defMultiply.target, new Multiply());
        }

        public override void Visit(AmlParser.DefDivide defDivide)
        {
            const int divisorLocal = AmlStackFrame.FirstReservedLocal;
            const int dividendLocal = divisorLocal + 1;

            // Push all operands on stack first, since subexpressions may use the reserved locals
            if (!IsNullTarget(defDivide.remainder.target)) {
                defDivide.remainder.target.Accept(this);
            }
            if (!IsNullTarget(defDivide.quotient.target)) {
                defDivide.quotient.target.Accept(this);
            }
            result.Add(new PushLocalObj(divisorLocal));
            defDivide.divisor.Accept(this);
            result.Add(new PushLocalObj(dividendLocal));
            defDivide.dividend.Accept(this);

            result.Add(new Store()); // Store dividend expression in dividendLocal
            result.Add(new Store()); // store divisor expression in divisorLocal

            if (!IsNullTarget(defDivide.quotient.target)) {
                result.Add(new PushLocalObj(divisorLocal));
                result.Add(new PushLocalObj(dividendLocal));
                result.Add(new Divide());
                result.Add(new Store()); // Store quotient in quotient.target
            }

            if (!IsNullTarget(defDivide.remainder.target)) {
                result.Add(new PushLocalObj(divisorLocal));
                result.Add(new PushLocalObj(dividendLocal));
                result.Add(new Remainder());
                result.Add(new Store()); // Store remainder in remainder.target
            }
        }

        public override void Visit(AmlParser.DefShiftLeft defShiftLeft)
        {
            VisitBinaryOperator(defShiftLeft.operand, defShiftLeft.shiftCount, defShiftLeft.target, new ShiftLeft());
        }
        
        public override void Visit(AmlParser.DefShiftRight defShiftRight)
        {
            VisitBinaryOperator(defShiftRight.operand, defShiftRight.shiftCount, defShiftRight.target, new ShiftRight());
        }
        
        public override void Visit(AmlParser.DefConcat defConcat)
        {
            VisitBinaryOperator(defConcat.leftData, defConcat.rightData, defConcat.target, new Concatenate());
        }

        public override void Visit(AmlParser.DebugObj debugObj)
        {
            result.Add(new PushDebugObj());
        }

        public override void Visit(AmlParser.DefDerefOf defDerefOf)
        {
            defDerefOf.objReference.Accept(this);
            result.Add(new DerefOf());
        }

        public override void Visit(AmlParser.DefMatch defMatch)
        {
            defMatch.startIndex.Accept(this);
            defMatch.operand2.Accept(this);
            defMatch.operand1.Accept(this);
            defMatch.searchPkg.Accept(this);
            result.Add(new Match(defMatch.matchOpcode1, defMatch.matchOpcode2));
        }

        public override void Visit(AmlParser.DefLEqual defLEqual)
        {
            defLEqual.rightOperand.Accept(this);
            defLEqual.leftOperand.Accept(this);
            result.Add(new LogicalOp(LogicalOp.Op.Equal));
        }

        public override void Visit(AmlParser.DefLLess defLLess)
        {
            defLLess.rightOperand.Accept(this);
            defLLess.leftOperand.Accept(this);
            result.Add(new LogicalOp(LogicalOp.Op.Less));
        }

        public override void Visit(AmlParser.DefLLessEqual defLLessEqual)
        {
            defLLessEqual.rightOperand.Accept(this);
            defLLessEqual.leftOperand.Accept(this);
            result.Add(new LogicalOp(LogicalOp.Op.LessEq));
        }

        public override void Visit(AmlParser.DefLGreater defLGreater)
        {
            defLGreater.rightOperand.Accept(this);
            defLGreater.leftOperand.Accept(this);
            result.Add(new LogicalOp(LogicalOp.Op.Greater));
        }

        public override void Visit(AmlParser.DefLGreaterEqual defLGreaterEqual)
        {
            defLGreaterEqual.rightOperand.Accept(this);
            defLGreaterEqual.leftOperand.Accept(this);
            result.Add(new LogicalOp(LogicalOp.Op.GreaterEq));
        }

        public override void Visit(AmlParser.DefLAnd defLAnd)
        {
            defLAnd.rightOperand.Accept(this);
            defLAnd.leftOperand.Accept(this);
            result.Add(new LogicalOp(LogicalOp.Op.And));
        }

        public override void Visit(AmlParser.DefLOr defLOr)
        {
            defLOr.rightOperand.Accept(this);
            defLOr.leftOperand.Accept(this);
            result.Add(new LogicalOp(LogicalOp.Op.Or));
        }

        public override void Visit(AmlParser.DefLNot defLNot)
        {
            defLNot.operand.Accept(this);
            result.Add(new LogicalOp(LogicalOp.Op.Not));
        }

        public override void Visit(AmlParser.DefAnd defAnd)
        {
            VisitBinaryOperator(defAnd.leftOperand, defAnd.rightOperand, defAnd.target,
                                new BitOp(BitOp.Op.And));
        }

        public override void Visit(AmlParser.DefOr defOr)
        {
            VisitBinaryOperator(defOr.leftOperand, defOr.rightOperand, defOr.target,
                                new BitOp(BitOp.Op.Or));
        }

        public override void Visit(AmlParser.DefNAnd defNAnd)
        {
            VisitBinaryOperator(defNAnd.leftOperand, defNAnd.rightOperand, defNAnd.target,
                                new BitOp(BitOp.Op.NAnd));
        }

        public override void Visit(AmlParser.DefNOr defNOr)
        {
            VisitBinaryOperator(defNOr.leftOperand, defNOr.rightOperand, defNOr.target,
                                new BitOp(BitOp.Op.NOr));
        }

        public override void Visit(AmlParser.DefNot defNot)
        {
            VisitUnaryOperator(defNot.operand, defNot.target,
                               new BitOp(BitOp.Op.Not));
        }

        public override void Visit(AmlParser.DefXOr defXOr)
        {
            VisitBinaryOperator(defXOr.leftOperand, defXOr.rightOperand, defXOr.target,
                                new BitOp(BitOp.Op.XOr));
        }

        private void VisitBinaryOperator(AmlParserNode left, AmlParserNode right,
                                         AmlParser.Target target, StackIRNode stackNode)
        {
            if (IsNullTarget(target)) {
                right.Accept(this);
                left.Accept(this);
                result.Add(stackNode);
            }
            else {
                target.Accept(this);
                right.Accept(this);
                left.Accept(this);
                result.Add(stackNode);
                result.Add(new Store());
            }
        }

        private void VisitUnaryOperator(AmlParserNode operand,
                                        AmlParser.Target target, StackIRNode stackNode)
        {
            if (IsNullTarget(target)) {
                operand.Accept(this);
                result.Add(stackNode);
            }
            else {
                target.Accept(this);
                operand.Accept(this);
                result.Add(stackNode);
                result.Add(new Store());
            }
        }

        public bool IsNullTarget(AmlParser.Target target)
        {
            SuperName superName = target.superName;
            if (superName.Tag != SuperName.TagValue.SimpleName) {
                return false;
            }
            SimpleName simpleName = superName.GetAsSimpleName();
            if (simpleName.Tag != SimpleName.TagValue.NameString) {
                return false;
            }
            NodePath nodePath = simpleName.GetAsNameString().nodePath;
            return (!nodePath.IsAbsolute &&
                    nodePath.NumParentPrefixes == 0 &&
                    nodePath.NameSegments.Length == 0);
        }

        public override void Visit(AmlParser.DefReturn defReturn)
        {
            defReturn.argObject.Accept(this);
            result.Add(new Return());
        }

        public override void Visit(AmlParser.DefWhile defWhile)
        {
            // We create a sequence like this:
            // jump to pushPredicate
            // loopback:
            // (body instructions)
            // pushPredicate:
            // (push predicate)
            // jump if not zero to loopback

            Jump jumpToPushPredicate = new Jump();
            JumpIfNonZero jumpLoopBack = new JumpIfNonZero();

            result.Add(jumpToPushPredicate);
            jumpLoopBack.ThenTarget = result.Count;
            VisitSequence(defWhile.termList);
            jumpToPushPredicate.Target = result.Count;
            defWhile.predicate.Accept(this);
            result.Add(jumpLoopBack);
        }

        public override void Visit(AmlParser.DefNotify defNotify)
        {
            defNotify.notifyValue.Accept(this);
            defNotify.notifyObject.Accept(this);
            result.Add(new Notify());
        }

        public override void Visit(AmlParser.DefSleep defSleep)
        {
            defSleep.msecTime.Accept(this);
            result.Add(new Sleep());
        }

        public override void Visit(AmlParser.DefCondRefOf defCondRefOf)
        {
            // We create a sequence like this:
            // jump if node path exists to existsBranch
            // (push 0)
            // jump to end
            // existsBranch:
            // (execute RefOf instruction and store to target)
            // (push 1)
            // end:

            // The only SuperName that can fail to exist is a node path
            if (defCondRefOf.superName.Tag == SuperName.TagValue.SimpleName &&
                defCondRefOf.superName.GetAsSimpleName().Tag == SimpleName.TagValue.NameString) {

                JumpIfNodePathExists existsJump = new JumpIfNodePathExists(
                    defCondRefOf.superName.GetAsSimpleName().GetAsNameString().nodePath);
                result.Add(existsJump);
                result.Add(new PushConst(new Integer(0)));
                Jump jumpOverExistsBranch = new Jump();
                result.Add(jumpOverExistsBranch);
                existsJump.ThenTarget = result.Count;

                defCondRefOf.target.Accept(this);
                defCondRefOf.superName.Accept(this);
                result.Add(new RefOf());
                result.Add(new Store());
                result.Add(new Discard());
                result.Add(new PushConst(new Integer(1)));

                jumpOverExistsBranch.Target = result.Count;
            }
            else {
                defCondRefOf.target.Accept(this);
                defCondRefOf.superName.Accept(this);
                result.Add(new RefOf());
                result.Add(new Store());
                result.Add(new Discard());
                result.Add(new PushConst(new Integer(1)));
            }
        }

        public override void Visit(AmlParser.DefOpRegion defOpRegion)
        {
            defOpRegion.regionLen.Accept(this);
            defOpRegion.regionOffset.Accept(this);
            result.Add(new StackIR.OperationRegion((RegionSpace)defOpRegion.regionSpace.byteData,
                                                   defOpRegion.nameString.nodePath));
        }
    
        public override void Visit(AmlParser.DefField defField)
        {
            result.Add(new Field(defField.fieldFlags, defField.nameString.nodePath, defField.fieldList));
        }

        public override void Visit(AmlParser.DefAcquire defAcquire)
        {
            defAcquire.mutexObject.Accept(this);
            result.Add(new Acquire(defAcquire.timeOut.wordData));
        }

        public override void Visit(AmlParser.DefRelease defRelease)
        {
            defRelease.mutexObject.Accept(this);
            result.Add(new Release());
        }

        public override void Visit(AmlParser.DefToBuffer defToBuffer)
        {
            defToBuffer.target.Accept(this);
            defToBuffer.operand.Accept(this);
            result.Add(new ToBuffer());
        }

        public override void Visit(AmlParser.DefToInteger defToInteger)
        {
            defToInteger.target.Accept(this);
            defToInteger.operand.Accept(this);
            result.Add(new ToInteger());
        }

        public override void Visit(AmlParser.DefToString defToString)
        {
            defToString.target.Accept(this);
            defToString.lengthArg.Accept(this);
            defToString.termArg.Accept(this);
            result.Add(new ToString());
        }

        public override void Visit(AmlParser.DefNoop defNoop)
        {
            // Do nothing
        }

        public override void Visit(AmlParser.DefLoad defLoad)
        {
            defLoad.ddbHandleObject.Accept(this);
            result.Add(new Load(defLoad.nameString.nodePath));
        }

        public override void Visit(AmlParser.DefStall defStall)
        {
            defStall.usecTime.Accept(this);
            result.Add(new Stall());
        }
    }
}
