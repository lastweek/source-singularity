// ==++==
//
//   Copyright (c) Microsoft Corporation.  All rights reserved.
//
// ==--==

// Verbose runtime tracing
//#define ENABLE_DEBUG_PRINT

// This class provides runtime support for managing delegates that may have
// been passed in to native code.
//
// The problem with these delegates is that the GC may move the delegate
// object without being aware of references from native code.  Rather than
// pinning the objects (which currently operates at a page granularity), we
// allocate GC-stable indexes ("delegate idxs") which the native code uses in
// place of the underlying Delegate reference.
//
// The entry points from compiled code are:
//
//   GetCodePtr, which allocates a short function to enter a delegate, passing
//   in the delegate idx.
//
//   ReleaseCodePtr, which deallocates the function and releases the delegate
//   idx.
//
// The NativeDelegateTable is used to map delegate idxs to Delegate references.
// References from this table are ordinary strong references as far as the GC
// is concerned.
namespace System
{

    using System.Reflection;
    using System.Runtime.InteropServices;
    using System.Runtime.CompilerServices;
    using System.Threading;

    //| <include path='docs/doc[@for="Delegate"]/*' />
    public abstract partial class Delegate : ICloneable
    {
        private IntPtr CodePtr;

        // equals returns true IIF the delegate is not null and has the
        //      same target, method and invocation list as this object
        //| <include path='docs/doc[@for="Delegate.Equals"]/*' />
        public override bool Equals(Object obj)
        {
            if (obj != null && obj is Delegate) {
                Delegate d = (Delegate) obj;
                if (IsStatic()) {
                    if (_methodPtrAux == d._methodPtrAux) {
                        return true;
                    }
                }
                else {
                    if (d._target == _target &&
                        d._methodPtr == _methodPtr) {
                        return true;
                    }
                }
            }
            return false;
        }

        //| <include path='docs/doc[@for="Delegate.GetHashCode"]/*' />
        public override int GetHashCode()
        {
            if (IsStatic())
                return this._methodPtrAux.ToInt32();
            else
                return this._methodPtr.ToInt32();
        }

        // Combine creates a new delegate based upon the contents of the
        //  delegates passed in.
        //| <include path='docs/doc[@for="Delegate.Combine"]/*' />
        public static Delegate Combine(Delegate a, Delegate b)
        {
            //@TODO: Should this really check to see that they are both multicast
            //      because it really is an error to try and combine non-multicasts?
            //      Spec says that it returns null and only does the check if a and b
            //      are both null.

            // boundary conditions -- if either (or both) delegates is null
            //      return the other.
            if (a == null)
                return b;
            if (b == null)
                return a;

            // Verify that the types are the same...
            if (a.GetType() != b.GetType())
                throw new ArgumentException("Arg_DlgtTypeMis");
            return  a.CombineImpl(b);
        }

        // This method creates a new delegate based upon the passed
        //  array of delegates.
        //| <include path='docs/doc[@for="Delegate.Combine1"]/*' />
        public static Delegate Combine(Delegate[] delegates)
        {
            if (delegates == null || delegates.Length == 0)
                return null;

            Delegate d = delegates[0];
            for (int i = 1; i < delegates.Length; i++)
                d = Combine(d,delegates[i]);
            return d;
        }

        // Return an array of delegates that represent the invocation list.
        // This is basically THIS for a Delegate.  MulticastDelegates may
        // have multiple members.
        //| <include path='docs/doc[@for="Delegate.GetInvocationList"]/*' />
        public virtual Delegate[] GetInvocationList() {
            Delegate[] d = new Delegate[1];
            d[0] = this;
            return d;
        }

        // This routine will return the target
        //| <include path='docs/doc[@for="Delegate.Target"]/*' />
        public Object Target
        {
            get {return IsStatic() ? null : _target;}
        }



        //A quick test to see if this is a delegate to a static method.
        //@ToDo: Verify that this is a sufficient test.
        private bool IsStatic() {
            if (_target is Delegate) {
                return true;
            }
            return false;
        }

        // This will remove the value delegate from the source delegate
        //  if it found.
        //| <include path='docs/doc[@for="Delegate.Remove"]/*' />
        public static Delegate Remove(Delegate source, Delegate value)
        {
            if (source == null)
                return null;
            if (value == null)
                return source;
            return source.RemoveImpl(value);
        }

        //| <include path='docs/doc[@for="Delegate.RemoveAll"]/*' />
        public static Delegate RemoveAll(Delegate source, Delegate value)
        {
            Delegate newDelegate = null;
            do {
                newDelegate = source;
                source = Remove(source, value);
            } while (newDelegate != source);
            return newDelegate;
        }

        // This is an internal routine that is called to do the combine.  We
        //  use this to do the combine because the Combine routines are static
        //  final methods.  In Delegate, this simply throws a MulticastNotSupportedException
        //  error.  Multicast delegate must implement this.
        //| <include path='docs/doc[@for="Delegate.CombineImpl"]/*' />
        protected virtual Delegate CombineImpl(Delegate d)
        {
            throw new MulticastNotSupportedException("Multicast_Combine");
        }

        // This is an internal routine that is called to do the remove.  We use this
        //  to do the remove because Remove is a static final method.  Here we simply
        //  make sure that d is equal to this and return null or this.
        //| <include path='docs/doc[@for="Delegate.RemoveImpl"]/*' />
        protected virtual Delegate RemoveImpl(Delegate d)
        {
            if (_target == d._target && _methodPtr == d._methodPtr)
                return null;
            else
                return this;
        }

        //| <include path='docs/doc[@for="Delegate.Clone"]/*' />
        public virtual Object Clone()
        {
            return MemberwiseClone();
        }

        //| <include path='docs/doc[@for="Delegate.operatorEQ"]/*' />
        public static bool operator ==(Delegate d1, Delegate d2) {
            if ((Object)d1 == null)
                return (Object)d2 == null;
            return d1.Equals(d2);
        }

        //| <include path='docs/doc[@for="Delegate.operatorNE"]/*' />
        public static bool operator != (Delegate d1, Delegate d2) {
            if ((Object)d1 == null)
                return (Object)d2 != null;
            return !d1.Equals(d2);
        }

        // GetCodePtr should be called by the marshalling code with the
        // delegate and the address of the call back stub for that
        // delegate class.
        [RequiredByBartok]
        private static IntPtr GetCodePtr(Delegate d,IntPtr callBackStub)
        {
            IntPtr codePtr = d.CodePtr;
            if (codePtr == IntPtr.Zero) {

                CriticalSection.AcquireMutex();
                try {
                    codePtr = d.CodePtr;
                    if (codePtr == IntPtr.Zero) {
                        int idx = AllocateNativeDelegateRecord(d);
                        codePtr = CreateCodePtr(idx, callBackStub);
                        d.CodePtr = codePtr;
                    }
                }
                finally {
                    CriticalSection.ReleaseMutex();
                }
            }
            return codePtr;
        }

        //////////////////////////////////////////////////////////////////////
        //
        internal static IntPtr FixedAlloc(int sizetdwBytes)
        {
            VTable.DebugBreak();
            return IntPtr.Zero;
        }

        internal static void FixedFree(IntPtr handle)
        {
            VTable.DebugBreak();
        }

        // Create a little piece of assembly code that adds idx onto the
        // argument list (by pushing it onto the stack) and jumps to the
        // call back stub.

        // The idx is added as the first argument.   The calling
        // convention is assumed to be STDCALL.
        //
        // The call back stub is a function created by the Bartok code
        // generator and:
        // 1. Uses the idx to get to the delegate via the NativeDelegateTable
        // 2. Calls the invoke method of the delegate

        private static unsafe IntPtr CreateCodePtr(int idx,
                                                   IntPtr callBackStub) {
            IntPtr buffer = FixedAlloc(32);
            if (buffer == IntPtr.Zero) {
                return IntPtr.Zero;
            }
            // The desired instructions:
            //      push [sp]
            //      mov [sp+4], idx
            //      jmp callBackStub
            //
            byte*  codeBuffer = (byte *) buffer.ToPointer();
            // push [sp]
            *(codeBuffer) = 0xFF;
            *(codeBuffer+1) = 0x34;
            *(codeBuffer+2) = 0x24;
            // mov [sp+4], idx
            *(codeBuffer+3) = 0xC7;
            *(codeBuffer+4) = 0x44;
            *(codeBuffer+5) = 0x24;
            *(codeBuffer+6) = 0x04;
            *((int*) (codeBuffer+7)) = idx;
            // jmp callBackStub
            *(codeBuffer+11) = 0xE9;
            IntPtr disp = callBackStub - buffer;
            *((int *) (codeBuffer+12)) = (disp - 16).ToInt32();
            //
            // pad the rest of the buffer with int 3
            //

            for (int i = 16; i < 32; i++) {
                *(codeBuffer+i) = 0xcc;
            }
            return buffer;
        }

        // This method accepts a code pointer and allows the NativeDelegateRecord
        // associated with it to be collected. In order to call this method
        // safely it must be certain that no references to the code ptr exist
        // in native code.
        private static unsafe void ReleaseCodePtr(IntPtr codePtr) {
            byte* codeBuffer = (byte *)codePtr.ToPointer();
            int idx = *(int*)(codeBuffer+7);
            Delegate del = IdxToDelegate(idx);
            del.CodePtr = IntPtr.Zero;
            CriticalSection.AcquireMutex();
            try {
                FreeNativeDelegateRecord(idx);
            }
            finally {
                CriticalSection.ReleaseMutex();
            }
            FixedFree(codePtr);
        }

        // <summary>
        // The CriticalSection protects the CodePtr fields during
        // initialization and the NativeDelegateTable arrays when claiming
        // indexes in them.
        // </summary>
        private static readonly Mutex CriticalSection;

        // <summary>
        // The NativeDelegateTable is held as a triangular array, starting
        // with small arrays of NativeDelegateRecord structures and using
        // successively larger arrays as the table is expanded.  This avoids
        // frequent allocations in programs that pass a lot of delegates
        // to native code, and allows an idx to map to a (table,offset) pair
        // in O(log n) steps.
        // </summary>
        private static NativeDelegateRecord[][] NativeDelegateTable;

        // In a debug build, start the NativeDelegateTable size very small in order to
        // force testing of table expansion
#if DEBUG
        private const int FIRST_TABLE_SIZE = 1;
#else
        private const int FIRST_TABLE_SIZE = 16;
#endif

        // <summary>
        // FreeListStartIdx is the idx is the head of the list of NativeDelegateTable
        // entries that have been freed.  -1 indicates that the free list is empty.
        // </summary>
        private static int FreeListStartIdx;
        private const int FREE_LIST_EMPTY = -1;

        // <summary>
        // FreeExtentStartIdx is the idx of the start of the contiguous
        // extent of NativeDelegateTable entries.  These are logically
        // considered at the end of the free list: we use entries from the free
        // list in preference to using 'pristine' space from the free extent.
        // </summary>
        private static int FreeExtentStartIdx;

        // <summary>
        // Each entry in the NativeDelegateTable currently holds an ordinary
        // reference to the Delegate and an integer used to form the free list
        // of unused records.  We could overload a single field, but note that
        // (a) we would then need to special-case the GC visiting code and
        // that (b) during GC we could not simply iterate through the arrays because
        // we couldn't distinguish free-list entries for allocated ones.
        //
        // Of course, we could steal a bit in the object reference to distinguish
        // the free list, using odd values for the free list to avoid needing
        // to mask the contents in IdxToDelegate.
        //
        // Seems like needless complexity unless we find the table is getting
        // large.
        // </summary>
        private struct NativeDelegateRecord {
            Delegate del;
            int nextIdx;

            internal void Allocate(Delegate del) {
                VTable.Assert(this.del == null);
                this.del = del;
            }

            internal void DeAllocate(int nextIdx) {
                VTable.Assert(this.del != null);
                this.del = null;
                this.nextIdx = nextIdx;
            }

            internal Delegate Delegate() {
                VTable.Assert(this.del != null);
                return this.del;
            }

            internal int NextIdx() {
                VTable.Assert(this.del == null);
                return this.nextIdx;
            }
        }

        // Allocate a native delegate record for "del".  The caller must hold
        // the CriticalSection.
        private static int AllocateNativeDelegateRecord(Delegate del) {
            int idx;
            int table;
            int offset;

            DebugPrint("AllocateNativeDelegateRecord (list={0}, extent {1})\n",
                       __arglist(FreeListStartIdx, FreeExtentStartIdx));

            if (FreeListStartIdx != FREE_LIST_EMPTY) {
                // There's space in the free list: use that
                int nextFreeIdx;
                idx = FreeListStartIdx;
                SplitIdx (idx, out table, out offset);
                nextFreeIdx = NativeDelegateTable[table][offset].NextIdx();
                FreeListStartIdx = nextFreeIdx;
            }
            else {
                // There's no space in the free list, use the next slot in the
                // free extent.
                idx = FreeExtentStartIdx;
                SplitIdx (idx, out table, out offset);
                FreeExtentStartIdx ++;
                if (offset + 1 == NativeDelegateTable[table].Length) {
                    // We've used the last slot in the free extent: allocate some
                    // more.
                    int currentLength = NativeDelegateTable[table].Length;
                    int nextLength = currentLength * 2;
                    DebugPrint("AllocateNativeDelegateRecord expanding to {0} len {1}\n",
                               __arglist(table + 1, nextLength));
                    NativeDelegateTable[table + 1] = new NativeDelegateRecord[nextLength];
                }
            }

            NativeDelegateTable[table][offset].Allocate(del);

            DebugPrint("AllocateNativeDelegateRecord got {0} (list={1}, extent {2})\n",
                       __arglist(idx, FreeListStartIdx, FreeExtentStartIdx));

            return idx;
        }

        private static void FreeNativeDelegateRecord(int idx) {
            int table;
            int offset;

            DebugPrint("FreeNativeDelegateRecord {0} (list={1}, extent {2})\n",
                       __arglist(idx, FreeListStartIdx, FreeExtentStartIdx));

            SplitIdx (idx, out table, out offset);
            NativeDelegateTable[table][offset].DeAllocate(FreeListStartIdx);
            FreeListStartIdx = idx;
        }

        [RequiredByBartok]
        private static Delegate IdxToDelegate(int idx) {
            int table;
            int offset;
            Delegate result;

            SplitIdx (idx, out table, out offset);
            result = NativeDelegateTable[table][offset].Delegate();
            DebugPrint("IdxToDelegate {0} -> {1}\n", __arglist(idx, result));

            return result;
        }

        private static void SplitIdx(int idx, out int table, out int offset) {
            table = 0;
            offset = idx;
            while (offset >= NativeDelegateTable[table].Length) {
                offset -= NativeDelegateTable[table].Length;
                table ++;
            }
            DebugPrint("SplitIdx {0} -> {1}.{2}\n", __arglist(idx, table, offset));
        }

        static Delegate() {
            CriticalSection = new Mutex();
            NativeDelegateTable = new NativeDelegateRecord[24][];
            NativeDelegateTable[0] = new NativeDelegateRecord[FIRST_TABLE_SIZE];
            FreeExtentStartIdx = 0;
            FreeListStartIdx = FREE_LIST_EMPTY;

#if FALSE // Enable this code to force testing of the FreeNativeDelegateRecord fn
            for (int i = 0; i < FIRST_TABLE_SIZE * 2; i ++) {
                int idx = AllocateNativeDelegateRecord(CriticalSection);
                VTable.Assert (idx == i);
            }
            for (int i = 0; i < FIRST_TABLE_SIZE * 2; i ++) {
                FreeNativeDelegateRecord(i);
            }
#endif
        }

        [System.Diagnostics.Conditional("ENABLE_DEBUG_PRINT")]
        [NoInline]
        internal static void DebugPrint(String v, __arglist)
        {
            VTable.DebugPrint(v, new ArgIterator(__arglist));
        }
    }
}
