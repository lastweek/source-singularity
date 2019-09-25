#if false
// ==++==
//
//   Copyright (c) Microsoft Corporation.  All rights reserved.
//
// ==--==
namespace System.Runtime.InteropServices
{

    using System;
    using System.Threading;
    using System.Runtime.CompilerServices;

    // These are the types of handles used by the EE.  IMPORTANT: These must
    // match the definitions in ObjectHandle.h in the EE.
    //| <include path='docs/doc[@for="GCHandleType"]/*' />
    public enum GCHandleType
    {
        //| <include path='docs/doc[@for="GCHandleType.Weak"]/*' />
        Weak = 0,
        //| <include path='docs/doc[@for="GCHandleType.WeakTrackResurrection"]/*' />
        WeakTrackResurrection = 1,
        //| <include path='docs/doc[@for="GCHandleType.Normal"]/*' />
        Normal = 2,
        //| <include path='docs/doc[@for="GCHandleType.Pinned"]/*' />
        Pinned = 3
    }

    // This class allows you to create an opaque, GC handle to any
    // managed object. A GC handle is used when an object reference must be
    // reachable from unmanaged memory.  There are 3 kinds of roots:
    // Normal - keeps the object from being collected.
    // Weak - allows object to be collected and handle contents will be zeroed.
    //          Weak references are zeroed before the finalizer runs, so if the
    //          object is resurrected in the finalizer the weak reference is
    //          still zeroed.
    // WeakTrackResurrection - Same as weak, but stays until after object is
    //          really gone.
    // Pinned - same as normal, but allows the address of the actual object
    //          to be taken.
    //
    //| <include path='docs/doc[@for="GCHandle"]/*' />
    [System.Runtime.InteropServices.StructLayout(LayoutKind.Sequential)]
    public struct GCHandle
    {
        // Allocate a handle storing the object and the type.
        internal GCHandle(Object value, GCHandleType type)
        {
            m_handle = InternalAlloc(value, type);

            // Record if the handle is pinned.
            if (type == GCHandleType.Pinned)
                m_handle |= 1;
        }

        // Used in the conversion functions below.
        internal GCHandle(IntPtr handle)
        {
            InternalCheckDomain((int) handle);
            m_handle = (int)handle;
        }

        // Creates a new GC handle for an object.
        //
        // value - The object that the GC handle is created for.
        // type - The type of GC handle to create.
        //
        // returns a new GC handle that protects the object.
        //| <include path='docs/doc[@for="GCHandle.Alloc"]/*' />
        public static GCHandle Alloc(Object value)
        {
            return new GCHandle(value, GCHandleType.Normal);
        }

        //| <include path='docs/doc[@for="GCHandle.Alloc1"]/*' />
        public static GCHandle Alloc(Object value, GCHandleType type)
        {
            return new GCHandle(value, type);
        }

        // Frees a GC handle.  The caller must provide synchronization to
        // prevent multiple threads from executing this simultaneously for
        // a given handle. If you modify this method please modify the
        // __InternalFree also which is the internal without the link-time check.
        //| <include path='docs/doc[@for="GCHandle.Free"]/*' />
        public void Free()
        {
            // Check if the handle was never initialized for was freed.
            if (m_handle == 0)
                throw new InvalidOperationException("InvalidOperation_HandleIsNotInitialized");

            // Free the handle.
            InternalFree(m_handle & ~0x1);
            m_handle = 0;
        }

        internal void __InternalFree()
        {
            // Check if the handle was never initialized for was freed.
            if (m_handle == 0)
                throw new InvalidOperationException("InvalidOperation_HandleIsNotInitialized");

            // Free the handle.
            InternalFree(m_handle & ~0x1);
            m_handle = 0;
        }

        // Target property - allows getting / updating of the handle's referent. If you modify this method

        // then modify the __InternalTarget too which is the internal method without the link-time check.
        //| <include path='docs/doc[@for="GCHandle.Target"]/*' />
        public Object Target
        {
            get
            {
                // Check if the handle was never initialized or was freed.
                if (m_handle == 0)
                    throw new InvalidOperationException("InvalidOperation_HandleIsNotInitialized");

                return InternalGet(m_handle & ~0x1);
            }

            set
            {
                // Check if the handle was never initialized or was freed.
                if (m_handle == 0)
                    throw new InvalidOperationException("InvalidOperation_HandleIsNotInitialized");

                InternalSet(m_handle & ~0x1, value, (m_handle & 0x1) != 0 /* isPinned */);
            }
        }

        internal Object __InternalTarget
        {
            get
            {
                // Check if the handle was never initialized or was freed.
                if (m_handle == 0)
                    throw new InvalidOperationException("InvalidOperation_HandleIsNotInitialized");

                return InternalGet(m_handle & ~0x1);
            }
        }

        // Retrieve the address of an object in a Pinned handle.  This throws
        // an exception if the handle is any type other than Pinned.
        //| <include path='docs/doc[@for="GCHandle.AddrOfPinnedObject"]/*' />
        public IntPtr AddrOfPinnedObject()
        {
            // Check if the handle was not a pinned handle.
            if ((m_handle & 1) == 0) {
                // Check if the handle was never initialized for was freed.
                if (m_handle == 0)
                    throw new InvalidOperationException("InvalidOperation_HandleIsNotInitialized");

                // You can only get the address of pinned handles.
                throw new InvalidOperationException("InvalidOperation_HandleIsNotPinned");
            }

            // Get the address.
            return InternalAddrOfPinnedObject(m_handle & ~0x1);
        }

        // Determine whether this handle has been allocated or not.
        //| <include path='docs/doc[@for="GCHandle.IsAllocated"]/*' />
        public bool IsAllocated
        {
            get
            {
                return m_handle != 0;
            }
        }

        // Used to create a GCHandle from an int.  This is intended to
        // be used with the reverse conversion.
        //| <include path='docs/doc[@for="GCHandle.operatorGCHandle"]/*' />
        public static explicit operator GCHandle(IntPtr value)
        {
            return new GCHandle(value);
        }

        // Used to get the internal integer representation of the handle out.
        //| <include path='docs/doc[@for="GCHandle.operatorIntPtr"]/*' />
        public static explicit operator IntPtr(GCHandle value)
        {
            return (IntPtr)value.m_handle;
        }

        // Internal native calls that this implementation uses.
        internal static int InternalAlloc(Object value, GCHandleType type)
        {
            int result, newIndex;
            if (type == GCHandleType.Pinned) {
                throw new Exception("GCHandle for pinned objects not yet implemented");
            }
            do {
                if (nextFreeIndex < 0) {
                    lock (handleToken) {
                        if (nextFreeIndex < 0) {
                            if (handleTable == null) {
                                handleTable = new HandleData[3];
                                handleTable[0].nextIndex = -1;
                                handleTable[1].nextIndex = 2;
                                handleTable[2].nextIndex = -1;
                                nextFreeIndex = 1;
                            }
                            else {
                                int oldLength = handleTable.Length;
                                int newLength = oldLength * 2;
                                HandleData[] newTable = new HandleData[newLength];
                                Array.Copy(handleTable, 0, newTable, 0, oldLength);
                                handleTable = newTable;
                                for (int i = oldLength + 1; i < newLength; i++) {
                                    handleTable[i].nextIndex = i + 1;
                                }
                                handleTable[newLength-1].nextIndex = -1;
                                nextFreeIndex = oldLength+1;
                            }
                        }
                    }
                }
                result = nextFreeIndex;
                newIndex = handleTable[result].nextIndex;
            } while (Interlocked.CompareExchange(ref nextFreeIndex, newIndex, result) != result);
            handleTable[result].obj = value;
            handleTable[result].type = type;
            // TODO: We should probably maintain a list of handles of each type
            return result;
        }

        internal static void InternalFree(int handle)
        {
            handleTable[handle].obj = null;
            int oldFreeIndex = nextFreeIndex;
            handleTable[handle].nextIndex = oldFreeIndex;
            while (Interlocked.CompareExchange(ref nextFreeIndex, handle, oldFreeIndex) != oldFreeIndex) {
                oldFreeIndex = nextFreeIndex;
                handleTable[handle].nextIndex = oldFreeIndex;
            }
        }

        internal static Object InternalGet(int handle)
        {
            return handleTable[handle].obj;
        }

        internal static void InternalSet(int handle, Object value, bool isPinned)
        {
            throw new Exception("System.Runtime.InteropServices.GCHandle.InternalSet not implemented in Bartok!");
        }

        internal static void InternalCompareExchange(int handle, Object value, Object oldValue, bool isPinned)
        {
            if (isPinned) {
                throw new Exception("CompareExchange on a pinned object?!?");
            }
            Interlocked.CompareExchange(ref handleTable[handle].obj, value, oldValue);
        }

        internal static IntPtr InternalAddrOfPinnedObject(int handle)
        {
            throw new Exception("System.Runtime.InteropServices.GCHandle.InternalAddrOfPinnedObject not implemented in Bartok!");
        }

        internal static void InternalCheckDomain(int handle)
        {
            throw new Exception("System.Runtime.InteropServices.GCHandle.InternalCheckDomain not implemented in Bartok!");
        }

        // The actual integer handle value that the EE uses internally.
        private int m_handle;

        private static HandleData[] handleTable;

        private static int nextFreeIndex = -1;

        private static Object handleToken = new Object();

        private struct HandleData {
            public Object obj;
            public GCHandleType type;
            public int nextIndex;
        }
    }
}
#endif

