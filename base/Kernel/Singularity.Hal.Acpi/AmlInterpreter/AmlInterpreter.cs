///////////////////////////////////////////////////////////////////////////////
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
//  Microsoft Research Singularity
//

// Interprets ACPI methods.

using System;
using System.Collections;
using System.Diagnostics;

using Node = Microsoft.Singularity.Hal.Acpi.AcpiNamespace.Node;
using NodePath = Microsoft.Singularity.Hal.Acpi.AcpiNamespace.NodePath;
using AbsoluteNodePath = Microsoft.Singularity.Hal.Acpi.AcpiNamespace.AbsoluteNodePath;

using Microsoft.Singularity.Hal.Acpi;
using Microsoft.Singularity.Hal.Acpi.AcpiObject;
using Microsoft.Singularity.Hal.Acpi.AmlParserUnions;
using Microsoft.Singularity.Hal.Acpi.StackIR;

namespace Microsoft.Singularity.Hal.Acpi
{
    public class InterpretException : Exception
    {
        public InterpretException() : base("Error interpreting AML") { }

        public InterpretException(string s) : base("Error interpreting AML: " + s) { }
    }

    public class MethodNotFoundInterpretException : Exception
    {
        public MethodNotFoundInterpretException() : base("Error interpreting AML: Method not found") { }

        public MethodNotFoundInterpretException(string s) : base("Error interpreting AML: Method not found: " + s) { }
    }

    public abstract class IoLocation
    {
        public abstract AcpiObject.AcpiObject Read();
        public abstract void Write(AcpiObject.AcpiObject value);
    }

    public class ValueIoLocation : IoLocation
    {
        private AcpiObject.AcpiObject value;

        public ValueIoLocation()
        {
            value = new UninitializedObject();
        }

        public ValueIoLocation(AcpiObject.AcpiObject acpiObject)
        {
            this.value = acpiObject;
        }

        public override AcpiObject.AcpiObject Read()
        {
            return value;
        }

        public override void Write(AcpiObject.AcpiObject value)
        {
            throw new InterpretException("Attempt to store to temporary object");
        }
    }

    public class DebugIoLocation : IoLocation
    {
        public override AcpiObject.AcpiObject Read()
        {
            throw new InterpretException("Attempt to read from debug object");
        }

        public override void Write(AcpiObject.AcpiObject value)
        {
#if SINGULARITY_KERNEL
            DebugStub.WriteLine("ACPI DEBUG: " + value.ToString());
#else
            Console.WriteLine("ACPI DEBUG: " + value.ToString());
#endif
        }
    }

    public class VariableIoLocation : ValueIoLocation
    {
        private AcpiObject.AcpiObject value;

        public VariableIoLocation()
        {
            value = new UninitializedObject();
        }

        public VariableIoLocation(AcpiObject.AcpiObject acpiObject)
        {
            value = acpiObject;
        }

        public override AcpiObject.AcpiObject Read()
        {
            return value;
        }

        public override void Write(AcpiObject.AcpiObject value)
        {
            this.value = value;
        }
    }

    public class NodePathIoLocation : ValueIoLocation
    {
        private AcpiNamespace.Node node;

        public NodePathIoLocation(AcpiNamespace.Node node)
        {
            if (node == null) {
                throw new ArgumentException("node should be non-null");
            }
            this.node = node;
        }

        public override AcpiObject.AcpiObject Read()
        {
            return node.Value;
        }

        public override void Write(AcpiObject.AcpiObject value)
        {
            node.Value = value;
        }
    }

    public class AmlStackFrame : IDisposable
    {
        // Local variable and argument objects
        public const int ReservedLocals = 2; // For use by the AmlStackIR compiler
        public const int FirstReservedLocal = 8;
        public const int NumLocals = FirstReservedLocal + ReservedLocals;
        VariableIoLocation[] locals = new VariableIoLocation[NumLocals];
        public const int NumArgs = 7;
        VariableIoLocation[] args = new VariableIoLocation[NumArgs];
        
        StackIRNode[] instructions;
        int currentInstructionIndex;

        private class AcpiNamespaceNodeSet : IEnumerable
        {
            private ArrayList nodeSet = new ArrayList();

            public void Add(AcpiNamespace.Node node)
            {
                if (!nodeSet.Contains(node)) {
                    nodeSet.Add(node);
                }
            }

            public IEnumerator GetEnumerator()
            {
                return nodeSet.GetEnumerator();
            }
        }

        AcpiNamespaceNodeSet methodTemporaryNamespaceObjectSet = new AcpiNamespaceNodeSet();

        public AmlStackFrame(StackIRNode[] instructions, AcpiObject.AcpiObject[] args)
        {
            this.instructions = instructions;
            currentInstructionIndex = 0;
            
            int i;
            for (i = 0; i < locals.Length; i++) {
                locals[i] = new VariableIoLocation();
            }
            for (i = 0; i < args.Length; i++) {
                this.args[i] = new VariableIoLocation(args[i]);
            }
            for (; i < this.args.Length; i++) {
                this.args[i] = new VariableIoLocation();
            }
        }

        public void NotifyCreateNodeAt(NodePath nodePath, Node node)
        {
            methodTemporaryNamespaceObjectSet.Add(node);
        }

        public void Dispose()
        {
            foreach (Node node in methodTemporaryNamespaceObjectSet) {
                node.Remove();
            }
        }

        public VariableIoLocation GetArgument(int argNum)
        {
            return args[argNum];
        }

        public void SetArgument(int argNum, AcpiObject.AcpiObject value)
        {
            args[argNum].Write(value);
        }

        public VariableIoLocation GetLocal(int localNum)
        {
            return locals[localNum];
        }

        public void SetLocal(int localNum, AcpiObject.AcpiObject value)
        {
            locals[localNum].Write(value);
        }

        public StackIRNode GetNextInstruction()
        {
            return instructions[currentInstructionIndex];
        }

        public void AdvanceInstruction()
        {
            currentInstructionIndex++;
        }
        
        public void JumpTo(int index)
        {
            currentInstructionIndex = index;
        }
    }

    public delegate void MethodResultCallback(AcpiObject.AcpiObject value);

    public class AmlInterpreterThread
    {
        private class AmlStack
        {
            private Stack stack = new Stack();

            public void Push(AmlStackFrame node)
            {
                stack.Push(node);
            }

            public AmlStackFrame Pop()
            {
                return (AmlStackFrame)stack.Pop();
            }

            public AmlStackFrame Peek()
            {
                return (AmlStackFrame)stack.Peek();
            }

            public bool IsEmpty()
            {
                return stack.Count == 0;
            }
        }

        private class IoLocationStack
        {
            private Stack stack = new Stack();

            public void Push(IoLocation node)
            {
                stack.Push(node);
            }

            public IoLocation Pop()
            {
                return (IoLocation)stack.Pop();
            }

            public IoLocation Peek()
            {
                return (IoLocation)stack.Peek();
            }
        }

        AcpiNamespace acpiNamespace;
        AbsoluteNodePath currentPath;
        AmlStack frameStack = new AmlStack();
        bool exited = false;
        bool blocked = false;
        AcpiObject.AcpiObject exitValue;
        IoLocationStack stack = new IoLocationStack();
        MethodResultCallback callback;
        IOperationRegionAccessor operationRegionAccessor;

        public AmlInterpreterThread(AcpiNamespace acpiNamespace, MethodResultCallback callback,
                                    IOperationRegionAccessor operationRegionAccessor)
        {
            this.acpiNamespace = acpiNamespace;
            this.currentPath = AbsoluteNodePath.CreateRoot();
            this.callback = callback;
            this.operationRegionAccessor = operationRegionAccessor;
        }

        public void InvokeMethod(Method method, AcpiObject.AcpiObject[] parameters)
        {
            method.Invoke(this, parameters, acpiNamespace);
        }

        public void InvokeMethod(AbsoluteNodePath nodePath, AcpiObject.AcpiObject[] parameters)
        {
            Node methodNode = acpiNamespace.LookupNode(nodePath);
            if (methodNode == null) {
                throw new MethodNotFoundInterpretException();
            }
            if (!(methodNode.Value is AcpiObject.BytecodeMethod)) {
                throw new AmlTypeException();
            }
            this.currentPath = methodNode.Path;
            ((AcpiObject.Method)(methodNode.Value)).Invoke(this, parameters, acpiNamespace);
        }

        public void PushFrame(AmlStackFrame frame)
        {
            frameStack.Push(frame);
        }

        public void Return(AcpiObject.AcpiObject result)
        {
            frameStack.Pop().Dispose();
            if (frameStack.IsEmpty()) {
                Exit(result);
            }
            else {
                Push(new ValueIoLocation(result));
            }
        }

        public AmlStackFrame CurrentFrame
        {
            get
            {
                return frameStack.Peek();
            }
        }

        public IOperationRegionAccessor OperationRegionAccessor
        {
            get
            {
                return operationRegionAccessor;
            }
        }

        public void Step()
        {
            if (Exited || Blocked) {
                throw new InterpretException("Tried to step exited or blocked thread");
            }
            new InterpretStepVisitor(this).Step();
        }

        public bool Exited
        {
            get
            {
                return exited;
            }
        }

        public void Exit(AcpiObject.AcpiObject exitValue)
        {
            exited = true;
            this.exitValue = exitValue;
            if (callback != null) {
                callback(ExitValue);
            }
        }

        public AcpiObject.AcpiObject ExitValue
        {
            get
            {
                return exitValue;
            }
        }

        public bool Blocked
        {
            get
            {
                return blocked;
            }
        }

        public void Block()
        {
            blocked = true;
        }

        public void Notify()
        {
            blocked = false;
        }

        public Node LookupNode(NodePath nodePath)
        {
            return acpiNamespace.LookupNode(nodePath, currentPath);
        }

        public Node CreateNodeAt(NodePath nodePath)
        {
            Node node = acpiNamespace.CreateNodeAt(nodePath, currentPath);
            frameStack.Peek().NotifyCreateNodeAt(nodePath, node);
            return node;
        }

        public void Push(IoLocation location)
        {
            stack.Push(location);
        }

        public IoLocation Pop()
        {
            return stack.Pop();
        }
    }

    public class InterpretStepVisitor : StackIRNodeVisitor
    {
        AmlInterpreterThread thread;

        public InterpretStepVisitor(AmlInterpreterThread thread)
        {
            this.thread = thread;
        }

        private AmlStackFrame Frame
        {
            get
            {
                return thread.CurrentFrame;
            }
        }

        public void Step()
        {
            AmlStackFrame frame = Frame;
            frame.GetNextInstruction().Accept(this);
            if (!thread.Blocked && !thread.Exited) {
                frame.AdvanceInstruction();
            }
        }

        public override void Visit(Jump node)
        {
            Frame.JumpTo(node.Target - 1); // Minus one because IP will still advance
        }

        public override void Visit(JumpIfNonZero node)
        {
            AcpiObject.AcpiObject predicate = thread.Pop().Read();
            if (predicate.GetAsInt().Value != 0) {
                Frame.JumpTo(node.ThenTarget - 1); // Minus one because IP will still advance
            }
        }

        public override void Visit(JumpIfNodePathExists node)
        {
            if (thread.LookupNode(node.NodePath) != null) {
                Frame.JumpTo(node.ThenTarget - 1); // Minus one because IP will still advance
            }
        }

        public override void Visit(PushArgObj node)
        {
            thread.Push(Frame.GetArgument(node.ArgNum));
        }

        public override void Visit(PushLocalObj node)
        {
            thread.Push(Frame.GetLocal(node.LocalNum));
        }

        public override void Visit(PushDebugObj node)
        {
            thread.Push(new DebugIoLocation());
        }

        public override void Visit(PushNodePath node)
        {
            Node pathNode = thread.LookupNode(node.Value);
            thread.Push(new NodePathIoLocation(pathNode));
            if (pathNode.Value is Method && pathNode.Value.GetAsMethod().ArgCount == 0) {
                Visit(new MethodCall());
            }
        }

        public override void Visit(PushConst node)
        {
            thread.Push(new ValueIoLocation(node.Value));
        }

        public override void Visit(Discard node)
        {
            thread.Pop();
        }

        public override void Visit(Store node)
        {
            IoLocation value = thread.Pop();
            IoLocation destination = thread.Pop();
            destination.Write(value.Read());
            thread.Push(destination);
        }

        public override void Visit(MethodCall node)
        {
            IoLocation methodLocation = thread.Pop();
            Method method = methodLocation.Read().GetAsMethod();
            
            AcpiObject.AcpiObject[] args = new AcpiObject.AcpiObject[method.ArgCount];
            for (int i = 0; i < method.ArgCount; i++) {
                args[i] = thread.Pop().Read();
            }

            thread.InvokeMethod(method, args);
        }

        public override void Visit(Index node)
        {
            AcpiObject.AcpiObject container = thread.Pop().Read();
            ulong index = thread.Pop().Read().GetAsInt().Value;
            thread.Push(new ValueIoLocation(new AcpiObject.BufferField(container, index * 8, 8)));
        }

        public override void Visit(ShiftLeft node)
        {
            ulong left = thread.Pop().Read().GetAsInt().Value;
            ulong right = thread.Pop().Read().GetAsInt().Value;
            PushInteger(left << (int)right);
        }

        public override void Visit(ShiftRight node)
        {
            ulong left = thread.Pop().Read().GetAsInt().Value;
            ulong right = thread.Pop().Read().GetAsInt().Value;
            PushInteger(left >> (int)right);
        }

        public override void Visit(Concatenate node)
        {
            AcpiObject.AcpiObject leftObj = thread.Pop().Read();
            AcpiObject.AcpiObject rightObj = thread.Pop().Read();

            if (leftObj is AcpiObject.String) {
                string leftStr = leftObj.GetAsString().Value;
                string rightStr = rightObj.GetAsString().Value;
                thread.Push(new ValueIoLocation(new AcpiObject.String(leftStr + rightStr)));
            }
            else {
                throw new InterpretException("Concatenate only implemented for strings");
            }
        }

        public override void Visit(Add node)
        {
            ulong left = thread.Pop().Read().GetAsInt().Value;
            ulong right = thread.Pop().Read().GetAsInt().Value;
            PushInteger(left + right);
        }

        public override void Visit(Subtract node)
        {
            ulong left = thread.Pop().Read().GetAsInt().Value;
            ulong right = thread.Pop().Read().GetAsInt().Value;
            PushInteger(left - right);
        }

        public override void Visit(Multiply node)
        {
            ulong left = thread.Pop().Read().GetAsInt().Value;
            ulong right = thread.Pop().Read().GetAsInt().Value;
            PushInteger(left * right);
        }

        public override void Visit(Divide node)
        {
            ulong left = thread.Pop().Read().GetAsInt().Value;
            ulong right = thread.Pop().Read().GetAsInt().Value;
            PushInteger(left / right);
        }

        public override void Visit(Remainder node)
        {
            ulong left = thread.Pop().Read().GetAsInt().Value;
            ulong right = thread.Pop().Read().GetAsInt().Value;
            PushInteger(left % right);
        }

        public override void Visit(LogicalOp node)
        {
            ulong left = thread.Pop().Read().GetAsInt().Value;
            ulong right = 0;

            if (node.Operator != LogicalOp.Op.Not) {
                right = thread.Pop().Read().GetAsInt().Value;
            }

            switch (node.Operator) {
                case LogicalOp.Op.Less:
                    PushInteger(left < right ? 1u : 0u);
                    break;
                case LogicalOp.Op.LessEq:
                    PushInteger(left <= right ? 1u : 0u);
                    break;
                case LogicalOp.Op.Equal:
                    PushInteger(left == right ? 1u : 0u);
                    break;
                case LogicalOp.Op.Greater:
                    PushInteger(left > right ? 1u : 0u);
                    break;
                case LogicalOp.Op.GreaterEq:
                    PushInteger(left >= right ? 1u : 0u);
                    break;
                case LogicalOp.Op.And:
                    PushInteger(left != 0 && right != 0 ? 1u : 0u);
                    break;
                case LogicalOp.Op.Or:
                    PushInteger(left != 0 || right != 0 ? 1u : 0u);
                    break;
                case LogicalOp.Op.Not:
                    PushInteger(left == 0 ? 1u : 0u);
                    break;
            }
        }

        public override void Visit(BitOp node)
        {
            ulong left = thread.Pop().Read().GetAsInt().Value;
            ulong right = 0;

            if (node.Operator != BitOp.Op.Not) {
                right = thread.Pop().Read().GetAsInt().Value;
            }

            switch (node.Operator) {
                case BitOp.Op.And:
                    PushInteger(left & right);
                    break;
                case BitOp.Op.Or:
                    PushInteger(left | right);
                    break;
                case BitOp.Op.NAnd:
                    PushInteger(~(left & right));
                    break;
                case BitOp.Op.NOr:
                    PushInteger(~(left | right));
                    break;
                case BitOp.Op.Not:
                    PushInteger(~left);
                    break;
                case BitOp.Op.XOr:
                    PushInteger(left ^ right);
                    break;
            }
        }

        public override void Visit(Return node)
        {
            thread.Return(thread.Pop().Read());
        }

        public override void Visit(CreateField node)
        {
            AcpiObject.Buffer sourceBuff = thread.Pop().Read().GetAsBuffer();
            ulong startBitIndex = thread.Pop().Read().GetAsInt().Value;
            ulong numBits = thread.Pop().Read().GetAsInt().Value;

            Node destinationNode = thread.CreateNodeAt(node.NodePath);
            destinationNode.Value = new BufferField(sourceBuff, startBitIndex, numBits);
        }

        public override void Visit(DefBuffer node)
        {
            ulong size = thread.Pop().Read().GetAsInt().Value;
            byte[] contents = new byte[size];
            byte[] initializer = node.Initializer;
            Array.Copy(initializer, contents, initializer.Length);
            thread.Push(new ValueIoLocation(new AcpiObject.Buffer(contents)));
        }

        public override void Visit(FindSetLeftBit node)
        {
            // Result: Zero indicates no bit set; k indicates the kth bit from the right is set
            ulong value = thread.Pop().Read().GetAsInt().Value;
            for (int i = 63; i >= 0; i--) {
                if (((value >> i) & 1) != 0) {
                    PushInteger((ulong)(i + 1));
                    return;
                }
            }
            PushInteger(0);
        }

        public override void Visit(FindSetRightBit node)
        {
            // Result: Zero indicates no bit set; k indicates the kth bit from the right is set
            ulong value = thread.Pop().Read().GetAsInt().Value;
            for (ulong i = 1; i <= 64; i++) {
                if ((value & 1) != 0) {
                    PushInteger(i);
                    return;
                }
                value >>= 1;
            }
            PushInteger(0);
        }

        public override void Visit(SizeOf node)
        {
            PushInteger(thread.Pop().Read().Size);
        }

        public override void Visit(DefName node)
        {
            Node namespaceNode = thread.CreateNodeAt(node.NodePath);
            namespaceNode.Value = thread.Pop().Read();
        }

        public override void Visit(Load node)
        {
            throw new InterpretException("TODO");
        }

        public override void Visit(Stall node)
        {
            throw new InterpretException("TODO");
        }

        public override void Visit(Match node)
        {
            throw new InterpretException("TODO");
        }

        public override void Visit(DerefOf node)
        {
            thread.Push(new ValueIoLocation(thread.Pop().Read().Dereference()));
        }

        public override void Visit(StackIR.Package node)
        {
            throw new InterpretException("TODO");
        }

        private void PushInteger(ulong i)
        {
            thread.Push(new ValueIoLocation(new AcpiObject.Integer(i)));
        }

        public override void Visit(Notify node)
        {
            throw new InterpretException("TODO");
        }

        public override void Visit(Sleep node)
        {
            throw new InterpretException("TODO");
        }

        public override void Visit(RefOf node)
        {
            // TODO: This implementation is not strictly correct, as it
            // will not continue to refer to the location if its value is
            // replaced (as can happen if it's currently uninitialized).
            // But currently the result of RefOf isn't used on any of
            // the tested machines, so postponing this.
            thread.Push(new ValueIoLocation(new AcpiObject.ObjectReference(new AcpiObjectCell(thread.Pop().Read()))));
        }

        public override void Visit(StackIR.OperationRegion node)
        {
            ulong startIndex = thread.Pop().Read().GetAsInt().Value;
            ulong length = thread.Pop().Read().GetAsInt().Value;

            Node namespaceNode = thread.CreateNodeAt(node.NodePath);
            namespaceNode.Value = new AcpiObject.OperationRegion(thread.OperationRegionAccessor,
                                                                 node.OperationSpace,
                                                                 startIndex, length);
        }

        public override void Visit(Field node)
        {
            Node operationRegionNode = thread.LookupNode(node.NodePath);
            SortedList fields = FieldUnit.CreateFromFieldList((AcpiObject.OperationRegion)(operationRegionNode.Value.GetTarget()),
                                                              node.FieldElements,
                                                              node.FieldFlags.accessType, AccessAttrib.SMBNone,
                                                              node.FieldFlags.lockRule, node.FieldFlags.updateRule);
            foreach (DictionaryEntry entry in fields) {
                Node namespaceNode = thread.CreateNodeAt(
                    new NodePath(false/*isAbsolute*/, 0, new string[] { (string)entry.Key }));
                namespaceNode.Value = (FieldUnit)entry.Value;
            }
        }

        public override void Visit(Acquire node)
        {
            Mutex mutex = thread.Pop().Read().GetAsMutex();
            mutex.Acquire(thread);
        }

        public override void Visit(Release node)
        {
            Mutex mutex = thread.Pop().Read().GetAsMutex();
            mutex.Release(thread);
        }

        public override void Visit(ToBuffer node)
        {
            throw new InterpretException("TODO");
        }

        public override void Visit(ToInteger node)
        {
            throw new InterpretException("TODO");
        }

        public override void Visit(ToString node)
        {
            throw new InterpretException("TODO");
        }
    }

    public class AmlInterpreter
    {
        private class AmlInterpreterThreadList : IEnumerable
        {
            Queue queue = new Queue();

            public void Enqueue(AmlInterpreterThread thread)
            {
                queue.Enqueue(thread);
            }

            public AmlInterpreterThread Dequeue()
            {
                return (AmlInterpreterThread)queue.Dequeue();
            }

            public IEnumerator GetEnumerator()
            {
                return queue.GetEnumerator();
            }

            public int Count
            {
                get
                {
                    return queue.Count;
                }
            }
        }

        AmlInterpreterThreadList threadsReadyToRun = new AmlInterpreterThreadList();
        AmlInterpreterThreadList threadsBlocked = new AmlInterpreterThreadList();
        AcpiNamespace acpiNamespace;
        IOperationRegionAccessor operationRegionAccessor;

        public AmlInterpreter(AcpiNamespace acpiNamespace,
                              IOperationRegionAccessor operationRegionAccessor)
        {
            this.acpiNamespace = acpiNamespace;
            this.operationRegionAccessor = operationRegionAccessor;
        }

        public AmlParser.ParseSuccess ParseMethodBodies()
        {
            foreach (Node node in acpiNamespace.GetAllNodes()) {
                if (!(node.Value is AcpiObject.BytecodeMethod)) {
                    continue;
                }

                AcpiObject.BytecodeMethod method = (AcpiObject.BytecodeMethod)node.Value;

#if SINGULARITY_KERNEL
                DebugStub.WriteLine("Parsing method " + node.Path.ToString());
#else
                Console.WriteLine("Parsing method " + node.Path.ToString());
#endif

                if (method.Parse(acpiNamespace, node.Path) == AmlParser.ParseSuccess.Failure) {
                    return AmlParser.ParseSuccess.Failure;
                }
            }
            return AmlParser.ParseSuccess.Success;
        }

        public AmlInterpreterThread InvokeMethodOnNewThread(MethodResultCallback callback,
                                                            AbsoluteNodePath nodePath, AcpiObject.AcpiObject[] parameters)
        {
            AmlInterpreterThread thread = new AmlInterpreterThread(acpiNamespace, callback, operationRegionAccessor);
            thread.InvokeMethod(nodePath, parameters);
            threadsReadyToRun.Enqueue(thread);
            return thread;
        }

        public void Run()
        {
            while (threadsReadyToRun.Count > 0) {
                while (threadsReadyToRun.Count > 0) {
                    AmlInterpreterThread currentThread = threadsReadyToRun.Dequeue();
                    while (!currentThread.Blocked && !currentThread.Exited) {
                        currentThread.Step();
                    }
                    if (currentThread.Blocked) {
                        threadsBlocked.Enqueue(currentThread);
                    }
                }
                foreach (AmlInterpreterThread thread in threadsBlocked) {
                    if (!thread.Blocked) {
                        threadsReadyToRun.Enqueue(thread);
                    }
                }
            }
            if (threadsBlocked.Count > 0) {
                throw new InterpretException("Deadlock between ACPI AML threads detected");
            }
        }
    }

    internal class ByteBufferAmlStreamAdapter : IAmlStream
    {
        byte[] buffer;

        public ByteBufferAmlStreamAdapter(byte[] buffer)
        {
            this.buffer = buffer;
        }

        public byte ReadByteData(ref int offset)
        {
            try {
                byte result = buffer[offset];
                offset++;
                return result;
            }
            catch (System.IndexOutOfRangeException) {
                throw new EndOfAmlStreamException();
            }
        }

        public bool TryReadByteData(ref int offset, out byte result)
        {
            if (offset >= buffer.Length) {
                result = 0;
                return false;
            }
            else {
                result = buffer[offset];
                offset++;
                return true;
            }
        }

        public char ReadChar(ref int offset)
        {
            try {
                char result = (char)buffer[offset];
                offset++;
                return result;
            }
            catch (System.IndexOutOfRangeException) {
                throw new EndOfAmlStreamException();
            }
        }

        public byte[] ReadByteDataArray(ref int offset, int length)
        {
            try {
                byte[] result = new byte[length];
                System.Array.Copy(buffer, offset, result, 0, length);
                offset += length;
                return result;
            }
            catch (System.ArgumentException) {
                throw new EndOfAmlStreamException();
            }
            catch (System.IndexOutOfRangeException) {
                throw new EndOfAmlStreamException();
            }
        }

        public bool TryReadByteDataArray(ref int offset, int length, out byte[] result)
        {
            if (offset + length > buffer.Length) {
                result = null;
                return false;
            }
            else {
                result = new byte[length];
                System.Array.Copy(buffer, offset, result, 0, length);
                offset += length;
                return true;
            }
        }

        public UInt16 ReadWordData(ref int offset)
        {
            try {
                UInt16 result = (UInt16)(buffer[offset] +
                                             (((UInt16)buffer[offset + 1]) << 8));;
                offset += 2;
                return result;
            }
            catch (System.IndexOutOfRangeException) {
                throw new EndOfAmlStreamException();
            }
        }

        public UInt32 ReadDWordData(ref int offset)
        {
            try {
                UInt32 result = (UInt32)(buffer[offset] +
                                               (((UInt32)buffer[offset + 1]) << 8) +
                                               (((UInt32)buffer[offset + 2]) << 16) +
                                               (((UInt32)buffer[offset + 3]) << 24));
                offset += 4;
                return result;
            }
            catch (System.IndexOutOfRangeException) {
                throw new EndOfAmlStreamException();
            }
        }

        public UInt64 ReadQWordData(ref int offset)
        {
            try {
                UInt64 result = (UInt64)(buffer[offset] +
                                               (((UInt64)buffer[offset + 1]) << 8) +
                                               (((UInt64)buffer[offset + 2]) << 16) +
                                               (((UInt64)buffer[offset + 3]) << 24) +
                                               (((UInt64)buffer[offset + 4]) << 32) +
                                               (((UInt64)buffer[offset + 5]) << 40) +
                                               (((UInt64)buffer[offset + 6]) << 48) +
                                               (((UInt64)buffer[offset + 7]) << 56));
                offset += 8;
                return result;
            }
            catch (System.IndexOutOfRangeException) {
                throw new EndOfAmlStreamException();
            }
        }
    }
}