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
    [CCtorIsRunDuringStartup]
    [NoLoggingForUndo]
    [RequiredByBartok]
    public abstract partial class Delegate
    {
        // _method is the MethodInfo representing the target, this is set by
        //  InternalCreate.
        [RequiredByBartok]
        private IntPtr _methodPtr;

        // _target is the object we will invoke o
        [RequiredByBartok]
        private Object      _target;

        // In the case of a static method passed to a delegate, this field stores
        // whatever _methodPtr would have stored: and _methodPtr points to a
        // small thunk which removes the "this" pointer before going on
        // to _methodPtrAux.
        [RequiredByBartok]
        private IntPtr _methodPtrAux = IntPtr.Zero;

        // Protect the default constructor so you can't build a delegate
        internal Delegate() {}

        //
        // This is just designed to prevent compiler warnings.
        // This field is used from native, but we need to prevent the compiler warnings.
        //
#if _DEBUG
        private void DontTouchThis() {
            _methodPtr = IntPtr.Zero;
            _target = null;
        }
#endif

        // Rest of class must define the following two methods:

        // [RequiredByBartok]
        // private static IntPtr GetCodePtr(Delegate d,IntPtr callBackStub);

        // [RequiredByBartok]
        // private static Delegate IdxToDelegate(int idx);
    }
}
