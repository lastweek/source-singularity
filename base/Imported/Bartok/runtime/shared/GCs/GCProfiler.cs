//
// Copyright (c) Microsoft Corporation.   All rights reserved.
//

/*******************************************************************/
/*                           WARNING                               */
/* This file should be identical in the Bartok and Singularity     */
/* depots. Master copy resides in Bartok Depot. Changes should be  */
/* made to Bartok Depot and propagated to Singularity Depot.       */
/*******************************************************************/

namespace System.GCs
{

    using Microsoft.Bartok.Runtime;

    internal delegate
    void ProfileRootsDelegate(NonNullReferenceVisitor visitor);

    internal delegate
    void ProfileObjectsDelegate(SegregatedFreeList.ObjectVisitor visitor);

    // Receive notifications from the GC and deliver them to a profiler.  This class
    // should be subtyped and then an instance associated with the GC via
    // System.GC.SetProfiler().
#if SINGULARITY
    [CLSCompliant(false)]
#endif
    public abstract class GCProfiler
    {
        public GCProfiler()
        {
            rootVisitor = new RootVisitor(this);
            objectVisitor = new ObjectVisitor(this);
        }

        // To limit the size of the TCB, we make a strict separation between two APIs.
        // The trusted API is the one between the GC and this base GCProfiler.  The
        // untrusted API is the one between this base GCProfiler and any subtypes of
        // this profiler that actually generate useful profiles.

        // Trusted API between this base and the GC
        internal void NotifyShutdown()
        {
            Shutdown();
        }

        internal void NotifyPreGC(int generation)
        {
            PreGC(generation);
        }

        internal void NotifyPostGC(ProfileRootsDelegate profileRoots,
                                   ProfileObjectsDelegate profileObjects)
        {
            this.profileRoots = profileRoots;
            this.profileObjects = profileObjects;
            PostGC();
        }

        internal void NotifyAllocation(UIntPtr objAddr, Type type, UIntPtr size)
        {
            Allocation(objAddr, type, size);
        }

        // Untrusted API between this base and the concrete profiler subtype.  The
        // concrete subtype implements this.
        protected abstract void Shutdown();
        protected abstract void PreGC(int generation);
        protected abstract void PostGC();
        protected abstract void Allocation(UIntPtr objAddr, Type type, UIntPtr size);

        protected abstract void ScanOneRoot(UIntPtr objectAddress);

        protected abstract void StartScanOneObject(UIntPtr objectAddress, Type type, UIntPtr size);
        protected abstract void ScanOneObjectField(UIntPtr objectAddress);
        protected abstract void EndScanOneObject();

        // API for the concrete subtype to call back on the abstract base.  We must
        // not accept UIntPtrs, etc. from the untrusted subtype and operate on them
        // here!

        protected void ScanRoots()
        {
            profileRoots(rootVisitor);
        }

        protected void ScanObjects()
        {
            profileObjects(objectVisitor);
        }

        // And the rest is implementation detail.

        private RootVisitor             rootVisitor;
        private ObjectVisitor           objectVisitor;

        private ProfileRootsDelegate    profileRoots;
        private ProfileObjectsDelegate  profileObjects;

        // For one object, visit all the references it contains
        internal class OneObjectVisitor : NonNullReferenceVisitor
        {
            private GCProfiler profiler;

            public OneObjectVisitor(GCProfiler profiler)
            {
                this.profiler = profiler;
            }

            // The NonNullReferenceVisitor contract:
            internal unsafe override void Visit(UIntPtr *location)
            {
                profiler.ScanOneObjectField(*location);
            }
        }

        // Visit all the roots
        internal class RootVisitor : NonNullReferenceVisitor
        {
            private GCProfiler profiler;

            public RootVisitor(GCProfiler profiler)
            {
                this.profiler = profiler;
            }

            // The NonNullReferenceVisitor contract:
            internal unsafe override void Visit(UIntPtr *location)
            {
                profiler.ScanOneRoot(*location);
            }
        }

        // Visit all the objects in the heap
        internal class ObjectVisitor : SegregatedFreeList.ObjectVisitor
        {
            private GCProfiler          profiler;
            private OneObjectVisitor    oneObjectVisitor;

            public ObjectVisitor(GCProfiler profiler)
            {
                this.profiler = profiler;
                oneObjectVisitor = new OneObjectVisitor(profiler);
            }

            // The ObjectVisitor contract:
            // Must return the size of the visited object.
            internal override UIntPtr Visit(Object obj)
            {
                UIntPtr size = ObjectLayout.Sizeof(obj);
                UIntPtr objectAddress = Magic.addressOf(obj);
                profiler.StartScanOneObject(objectAddress, obj.GetType(), size);
                oneObjectVisitor.VisitReferenceFields(obj);
                profiler.EndScanOneObject();
                return size;
            }
        }
    }
}
