//
// Copyright (c) Microsoft Corporation.   All rights reserved.
//

/*******************************************************************/
/*                           WARNING                               */
/* This file should be identical in the Bartok and Singularity     */
/* depots. Master copy resides in Bartok Depot. Changes should be  */
/* made to Bartok Depot and propagated to Singularity Depot.       */
/*******************************************************************/


/*

This class provides fast-path code for a number of operations which
potentially require additional information to be associated with each
object in the heap:

 - Object ownership and versioning information needed by the STM
   implementation.

 - Location-insensitive hash codes that have been allocated to objects.

 - Monitor objects that have been associate with objects.

 - StringState bits associated with String objects


Overview
--------

Each object has a value of type MultiUseWord (MUW) held as a header
word.  This can be used directly for any *one* of the three purposes
listed above.  If more than one kind of usage is required on the same
object then the MUW is "inflated" -- i.e. replaced by a value that
indicates an external multi-use object (EMU) which contains space for
all three purposes.

NB: the StringState and HashCode words share the same storage locations,
distinguished by value.  We rely on ChooseHashCode to not use small
integer values corresponding to the StringState enumeration.

In addition, the MUW provides a single per-object 'mark' bit.  This
is used in the MemoryAccounting module when counting the volume of
different kinds of object in the heap.  Placing this bit in the MUW
(rather than using spare vtable-bits as the GC does) allows
memory accounting to be invoked at any time (e.g. after a crash during
a GC).

MUW structure
-------------

The structure of the MUW on a 32-bit system is as follows:

   | 31             3 | 2  | 1 0 |
   |       payload    |mark| tag |

And on a 64-bit system:

   | 63             3 | 2  | 1 0 |
   |       payload    |mark| tag |

On 32-bit systems, this allows us to support pointers through the entire
4 GB address range.  However, it means that pointers must be constrained
to fit in the limited space of the payload.  For instance, the Monitor
is 8-byte aligned so the low 3 bits are available for encoding the tag
and mark.

By convention, all modules using the mark bit must (a) work with the
world stopped and (b) leave all object's mark bits 0 after their operation.
(They may assume this is true when they start).  This restriction avoids
needing to mask off the mark bit in common code paths in this file.

The payload field forms the majority of the MUW.  The contents of the
payload are taken from bits 3..31 in the MUW, padded with three 0-bits
at the least significant end.  This means that the payload can hold a
pointer to an 8-byte aligned address.

The tag values distinguish between four states that the MUW can be in:

00 => The MUW is either unused (if the payload is 0), or holds the
      STM word for the object (if the payload is non-0).

01 => The payload holds the object's hash code or StringState bits.

10 => The payload refers to the object's Monitor.

11 => The payload refers to an external multi-use object (EMU).


Memory management
-----------------

See detailed comments below about interaction between this file and
the various garbage collectors.


To do
-----

 - If we can guarantee that the GC will not relocate objects then we
   can avoid needing to place hashcodes in the MUW.  This may
   slightly reduce the frequency of inflation.

 - The state used for fast-path monitor operations could be placed
   directly in the MUW's payload rather than in an external Monitor
   object.

*/

// Verbose runtime tracing
//#define ENABLE_LOG_TRACING

// Profile MUW inflation
#if DEBUG
#define ENABLE_PROFILING
#endif

// Occasionally perform unnecessary inflation
//#define SHAKE

namespace System {

    using Microsoft.Bartok.Runtime;
    using System.GCs;
    using System.Runtime.CompilerServices;
    using System.Threading;

    [CCtorIsRunDuringStartup]
    [NoLoggingForUndo]
    internal struct MultiUseWord {
        internal UIntPtr value;

        // Different tag values
        internal const uint STM_TAG       = 0;
        internal const uint HASHCODE_TAG  = 1;
        internal const uint MONITOR_TAG   = 2;
        internal const uint INFLATED_TAG  = 3;

        // Structure of the multi-use word
        internal const uint TAG_MASK  = 0x00000003;

        // Hash codes are restricted to positive int32, even on 64-bit systems.
        internal const int  HASHCODE_MASK = 0x7ffffff8;

        //----------------------------------------------------------------------
        //
        // Constructors

        static MultiUseWord() {
        }

        internal MultiUseWord(UIntPtr value) {
            this.value = value;
        }

        internal MultiUseWord(uint tag, UIntPtr payload) {
            VTable.Assert((tag & TAG_MASK) == tag);
            VTable.Assert((UIntPtr)(payload & PAYLOAD_MASK) == payload);
            this.value = (UIntPtr)(tag | (uint)payload);
            DebugPrint("MUW tag={0:x} uintptr-payload={1:x}\n",
                       __arglist(tag, payload));
        }

        // Objects encoded in the payload must be 8-byte aligned.  However,
        // this alignment refers to the object's data portion, so that is
        // what we store.
        internal MultiUseWord(uint tag, Object payload) {
            UIntPtr addr = Magic.addressOf(payload) + PostHeader.Size;
            VTable.Assert(!(payload is uint));
            VTable.Assert((tag == MONITOR_TAG) ||
                          (tag == INFLATED_TAG));
            VTable.Assert(payload != null);
            VTable.Assert((addr & PAYLOAD_MASK) == addr);
            VTable.Assert((addr & (payload.vtable.baseAlignment - 1)) == 0);
            this.value = (UIntPtr)((UIntPtr)tag |addr);
            DebugPrint("MUW tag={0:x} object-payload={1:x}\n",
                       __arglist(tag, Magic.addressOf(payload)));
        }

        //----------------------------------------------------------------------

        // Accessor methods

        internal uint GetTag() {
            uint tag = (uint)(this.value & INFLATED_TAG);
            return tag;
        }

        internal bool IsUnused() {
            bool result = (this.value == UIntPtr.Zero);
            return result;
        }

        internal bool IsMarked() {
            bool result = ((this.value & MARK_BIT_MASK) != 0);
            return result;
        }

        internal bool IsInflated() {
            bool result = ((this.value & TAG_MASK) == INFLATED_TAG);
            return result;
        }

        internal bool IsHashcode() {
            bool result = ((this.value & TAG_MASK) == HASHCODE_TAG);
            return result;
        }

        internal bool IsMonitor() {
            bool result = ((this.value & TAG_MASK) == MONITOR_TAG);
            return result;
        }

        internal bool IsMonitorOrInflatedTag() {
            bool result = (this.value & MONITOR_TAG) != 0;
            return result;
        }

        internal bool IsSTM() {
            bool result = ((this.value & TAG_MASK) == STM_TAG);
            return result;
        }

        internal bool Eq(MultiUseWord other) {
            return (other.value == this.value);
        }

        // Return the payload of the multi-use word as a UIntPtr.

        internal UIntPtr GetPayload() {
            UIntPtr result = (this.value & PAYLOAD_MASK);
            return result;
        }

        // Return the payload of the multi-use word as an object reference.
        // Asserts that the payload is non-null and that the object that it
        // refers to has strong enough alignment requirements for the number
        // of payload bits available.
        //
        // Recall that for objects we store a pointer to the data portion rather
        // than to the PostHeader, since this is what the caller has aligned.

        internal unsafe Object GetRefPayload() {
            UIntPtr payload = (UIntPtr) this.GetPayload();
            Object result = Magic.fromAddress(payload - PostHeader.Size);
            VTable.Assert(result != null);
            VTable.Assert(result.vtable != null);
            VTable.Assert((payload & (result.vtable.baseAlignment - 1)) == 0);
            return result;
        }

        // Equivalent to "(EMU) GetRefPayload()", but avoids an explicit
        // cast.  This is needed during GCs that use the vtable word.
        internal unsafe EMU GetEMURefPayload() {
            UIntPtr payload = (UIntPtr) this.GetPayload();
            EMU result = EMU.FromAddress(payload - PostHeader.Size);
            VTable.Assert(result != null);
            VTable.Assert((payload & (result.vtable.baseAlignment - 1)) == 0);
            return result;
        }

        //----------------------------------------------------------------------
        //
        // Get and set an object's MUW.

        [ManualRefCounts]
        internal static MultiUseWord GetForObject(Object obj) {
            MultiUseWord result = ((ObjectPreMUW) obj).muw;

            DebugPrint("GetForObject({0:x}) = {1:x}\n",
                       __arglist(Magic.addressOf(obj), result.value));

            return result;
        }

        [ManualRefCounts]
        internal static void SetForObject(Object obj, MultiUseWord w) {
            DebugPrint("SetForObject({0:x}, {1:x})\n",
                       __arglist(Magic.addressOf(obj), w.value));

            ((ObjectPreMUW) obj).muw = w;
        }

        private static
        MultiUseWord CompareExchangeForObject(Object obj,
                                              MultiUseWord newWord,
                                              MultiUseWord oldWord)
        {
            DebugPrint("CompareExchangeForObject({0:x}, new={1:x}, old={2:x})\n",
                       __arglist(Magic.addressOf(obj), newWord.value, oldWord.value));

            UIntPtr saw =
                CompareExchangeForObject(obj, newWord.value, oldWord.value);

            DebugPrint("CompareExchangeForObject saw {0:x}\n", __arglist(saw));

            return new MultiUseWord(saw);
        }

        internal static UIntPtr CompareExchangeForObject(Object obj,
                                                         UIntPtr newValue,
                                                         UIntPtr oldValue)
        {
            UIntPtr saw =
                ((ObjectPreMUW) obj).CompareExchangeMUW(newValue, oldValue);
            return saw;
        }

        // Get and set the underlying UIntPtr value held in the same
        // header word that is used for the MUW.  These methods are needed
        // in MemoryAccounting where the header field is re-used (after
        // making a private copy of the MUW value).

        [ManualRefCounts]
        internal static UIntPtr GetValForObject(Object obj) {
            UIntPtr result = GetForObject(obj).value;

            DebugPrint("GetValForObject({0:x}) = {1:x}\n",
                       __arglist(Magic.addressOf(obj), result));

            return result;
        }

        [ManualRefCounts]
        internal static void SetValForObject(Object obj, UIntPtr w) {
            DebugPrint("SeValtForObject({0:x}, {1:x})\n",
                       __arglist(Magic.addressOf(obj), w));

            SetForObject(obj, new MultiUseWord(w));
        }

        internal static UIntPtr PAYLOAD_MASK {
            get { return (UIntPtr.Size == 8)?
                (UIntPtr)0xfffffffffffffff8 :
                (UIntPtr)0xfffffff8; }
        }

        internal static UIntPtr MARK_BIT_MASK {
            get { return (UIntPtr)0x04; }
        }

        //----------------------------------------------------------------------
        //
        // Shake debugging
        //
        // If SHAKE is #defined then we periodically choose to inflate an
        // object's multi-use-word when it is not necessary to do so.  This
        // will help test coverage: this design is based on the assumption that
        // inflation is rare, so let's make sure that it actually works!
        //
        // Code guarded by "if (Occasionally()) { ... }" will run occasionally
        // when shake debugging is enabled, and should be entirely elided when
        // it is disabled.
        //
        // NB: Occasionally() is not thread safe, but note that even if races
        // allow shakeCtr to overshoot shakeLim then it doesn't matter: we'll
        // just go around another shakeLim times.

#if SHAKE
        private static int shakeCtr = 0;
        private static int shakeLim = 1;
#endif

        [Inline]
        internal static bool Occasionally() {
            bool result = false;
#if SHAKE
            if ((shakeCtr++) % shakeLim == 0) {
                shakeLim += 10;
                shakeCtr = 1;
                result = true;
            }
#endif
            return result;
        }

        //----------------------------------------------------------------------
        //
        // Mark bit

        internal static bool IsMarked(Object obj) {
            MultiUseWord muw = GetForObject(obj);
            bool result;
            result = muw.IsMarked();
            return result;
        }

        internal static void SetMark(Object obj, bool mark) {
            MultiUseWord muw = GetForObject(obj);
            MultiUseWord newMuw;
            if (mark) {
                newMuw = new MultiUseWord(muw.value | (UIntPtr)MARK_BIT_MASK);
            } else {
                newMuw = new MultiUseWord(muw.value & (UIntPtr)(~MARK_BIT_MASK));
            }
            SetForObject(obj, newMuw);
        }

        //----------------------------------------------------------------------
        //
        // Monitor
        //
        // The implementation of Monitor-related and Hashcode-related operations
        // is largely the same:
        //
        //   - A "Get..." method deals with the fast path operations of either:
        //     returning the Monitor/Hashcode directly from the MUW or from the
        //     field containing it in the EMU.
        //
        //   - A "Get...Slow" method is responsible for the slow path operations
        //     of allocating a new monitor/hashcode and inflating a MUW if
        //     necessary.

        [NoInline]
        internal static Monitor GetMonitorSlow(Object obj, MultiUseWord muw) {
            Monitor result = null;

            DebugPrint("GetMonitorSlow obj={0:x} muw={1:x}\n",
                       __arglist(Magic.addressOf(obj), muw.value));

            // .................................................................
            //
            // Firstly: try to allocate a Monitor object and make this reachable
            // directly from the MUW.

            if (muw.IsUnused() && (!Occasionally())) {
                MultiUseWord newWord;
                DebugPrint("MUW currently unused for {0:x}, allocating monitor\n",
                           __arglist(Magic.addressOf(obj)));

                // Remember: either of these allocations may trigger a GC.

                Monitor m = new Monitor();

#if REFERENCE_COUNTING_GC || DEFERRED_REFERENCE_COUNTING_GC
                DebugPrint("+rc on monitor {0:x}\n", __arglist(Magic.addressOf(m)));
                NonNullIncrementRefCount(m);
#else
                EMU emu = new EMU();
                IncrementMonitorEMUAllocCount();
                emu.Target = obj;
                emu.Monitor = m;
#endif

                newWord = new MultiUseWord(MONITOR_TAG, m);
                DebugPrint("MUW currently unused for {0:x}, trying to install {1:x}\n",
                           __arglist(Magic.addressOf(obj), newWord.value));

                MultiUseWord now = CompareExchangeForObject(obj, newWord, muw);

#if REFERENCE_COUNTING_GC || DEFERRED_REFERENCE_COUNTING_GC
                if (now.Eq(muw)) {
                    DebugPrint("Installed it\n");
                    RegisterLostObjForVerifyHeap(obj, m);
                } else {
                    DebugPrint("-rc on monitor {0:x}\n", __arglist(Magic.addressOf(m)));
                    NonNullDecrementRefCount(m);
                }
#else
                if (now.Eq(muw)) {
                    DebugPrint("Installed it\n");
                    emu.Register();
                } else {
                    IncrementAbandonedEMUsCount();
                }
#endif

                muw = GetForObject(obj);

                DebugPrint("MUW now {0:x}\n", __arglist(muw.value));
            }

            // .................................................................
            //
            // Secondly: either pick up the Monitor reachable from the MUW,
            // or from the EMU (inflating if necessary).

            uint tag = muw.GetTag();
            if (tag == MONITOR_TAG) {
                result = (Monitor)(muw.GetRefPayload());
            } else {
                if (tag != INFLATED_TAG) {
                    Inflate(obj);
                    IncrementInflationToCount(MONITOR_TAG);
                    muw = GetForObject(obj);
                    tag = muw.GetTag();
                }

                VTable.Assert(tag == INFLATED_TAG,
                              "Multi-use word not inflated in GetMonitorSlow");

                EMU emu = muw.GetEMURefPayload();

                VTable.Assert(emu.monitor != UIntPtr.Zero, "Monitor should not be null");

                result = emu.Monitor;
            }

            DebugPrint("Got monitor {0:x}\n", __arglist(Magic.addressOf(result)));
            return result;
        }

        internal static Monitor GetMonitor(Object obj) {
            Monitor result;

            DebugPrint("GetMonitor[Fast] obj={0:x} on {1:x} type {2:x}\n",
                       __arglist(Magic.addressOf(obj),
                                 PageTable.Page(Magic.addressOf(obj)),
                                 PageTable.MyType(PageTable.Page(Magic.addressOf(obj)))));

            MultiUseWord muw = GetForObject(obj);
            uint tag = muw.GetTag();

            DebugPrint("GetMonitor[Fast] muw={0:x} tag={1:x}\n",
                       __arglist(muw.value, tag));

            if (tag == MONITOR_TAG) {
                result = (Monitor)muw.GetRefPayload();
            } else {
                if (tag == INFLATED_TAG) {
                    EMU emu = muw.GetEMURefPayload();
                    if (emu.Monitor != null) {
                        result = emu.Monitor;
                    } else {
                        result = GetMonitorSlow(obj, muw);
                    }
                } else {
                    result = GetMonitorSlow(obj, muw);
                }
            }

            DebugPrint("Got monitor {0:x}\n", __arglist(Magic.addressOf(result)));

            return result;
        }

        //----------------------------------------------------------------------
        //
        // Hashcode
        //
        // See comments above regarding monitors.  The implementation of
        // hashcodes follows the same general pattern aside from the addition
        // of Get/SetStringState.

        [NoInline]
        internal static int GetHashCodeSlow(Object obj, MultiUseWord muw) {
            int result;

            DebugPrint("GetHashCodeSlow obj={0:x} muw={1:x}\n",
                       __arglist(Magic.addressOf(obj), muw.value));

            // .................................................................
            //
            // Firstly: try to choose a hash code place this directly in the MUW.

            if (muw.IsUnused() && (!Occasionally())) {
                MultiUseWord newWord;
                DebugPrint("MUW currently unused for {0:x}, choosing hash code\n",
                           __arglist(Magic.addressOf(obj)));
                int h = ChooseHashCode(obj);
                newWord = new MultiUseWord(HASHCODE_TAG, (UIntPtr) h);
                DebugPrint("MUW currently unused for {0:x}, trying to install {1:x}\n",
                           __arglist(Magic.addressOf(obj), newWord.value));
                CompareExchangeForObject(obj, newWord, muw);
                muw = GetForObject(obj);
                DebugPrint("MUW now {0:x}\n", __arglist(muw.value));
            }

            // .................................................................
            //
            // Secondly: either pick up the hash code from the MUW, or from the EMU
            // (inflating if necessary).

            uint tag = muw.GetTag();
            if (tag == HASHCODE_TAG) {
                result = (int)(muw.GetPayload());
            } else {
                if (tag != INFLATED_TAG) {
                    Inflate(obj);
                    IncrementInflationToCount(HASHCODE_TAG);
                    muw = GetForObject(obj);
                    tag = muw.GetTag();
                }

                VTable.Assert(tag == INFLATED_TAG,
                              "Multi-use word not inflated in GetHashCodeSlow");

                EMU emu = muw.GetEMURefPayload();

                result = emu.HashCode;
            }

            DebugPrint("Got hash code {0:x}\n", __arglist(result));
            return result;
        }

        internal static int GetHashCode(Object obj) {
            int result;

            DebugPrint("GetHashCode[Fast] obj={0:x}\n",
                       __arglist(Magic.addressOf(obj)));

            MultiUseWord muw = GetForObject(obj);
            uint tag = muw.GetTag();

            DebugPrint("GetHashCode[Fast] muw={0:x} tag={1:x}\n",
                       __arglist(muw.value, tag));

            if (tag == HASHCODE_TAG) {
                result = (int)(muw.GetPayload());
            } else {
                if (tag == INFLATED_TAG) {
                    EMU emu = muw.GetEMURefPayload();
                    result = emu.HashCode;
                } else {
                    return GetHashCodeSlow(obj, muw);
                }
            }

            DebugPrint("Got hash code {0:x}\n", __arglist(result));
            return result;
        }

        internal static StringState GetStringState(String str) {
            int result = GetHashCode(str);
            VTable.Assert(((result == (int)StringState.Undetermined) ||
                           (result == (int)StringState.HighChars) ||
                           (result == (int)StringState.FastOps) ||
                           (result == (int)StringState.SpecialSort)));
            return (StringState) result;
        }

        // Forcible set the StringState bits in the hashcode word.
        //
        // There is a subtle, benign and unlikely race in this code:
        // we may execute Interlocked.CompareExchange on the emu.HashCode
        // field at exactly the same time that another thread re-inflates
        // the object.  The current code loops until it successfully
        // writes the intended value into the hashcode field.  However,
        // note that if concurrent threads call SetHashCode then it might
        // be possible for a value to be re-written: the first thread
        // may update emu.HashCode, a second thread re-inflates the
        // object, a third thread then calls SetHashCode successfully
        // and then the first thread observes the race with the second
        // and writes its value again.  This race is benign for the
        // case of StringState flags: the value written depends on the
        // immutable contents of the string.

        internal static void SetStringState(String str, StringState st) {
            bool done = false;

            DebugPrint("SetStringState str={0:x} hashcode={1:x}\n",
                       __arglist(Magic.addressOf(str), st));

            do {
                MultiUseWord oldMUW = GetForObject(str);
                uint tag = oldMUW.GetTag();
                DebugPrint("SetStringState muw={0:x} tag={1:x}\n",
                           __arglist(oldMUW.value, tag));

                if ((oldMUW.IsUnused() && (!Occasionally())) ||
                    (tag == HASHCODE_TAG)) {
                    MultiUseWord newMUW = new MultiUseWord(HASHCODE_TAG,
                                                           (UIntPtr)st);
                    MultiUseWord sawMUW = CompareExchangeForObject(str,
                                                                   newMUW,
                                                                   oldMUW);
                    done = (sawMUW.Eq(oldMUW));
                } else {
                    if (tag != INFLATED_TAG) {
                        Inflate(str);
                        oldMUW = GetForObject(str);
                        tag = oldMUW.GetTag();
                    }

                    VTable.Assert(tag == INFLATED_TAG,
                                  "Multi-use word not inflated in SetStringState");

                    EMU emu = oldMUW.GetEMURefPayload();
                    int oldStringState = emu.hashCode;
                    int sawStringState = Interlocked.CompareExchange(ref emu.hashCode,
                                                                  (int)st,
                                                                  oldStringState);
                    MultiUseWord newMUW = GetForObject(str);

                    done = ((sawStringState == oldStringState) &&
                            (newMUW.Eq(oldMUW)));
                }
            } while (!done);

            VTable.Assert(GetHashCode(str) == (int)st,
                          "HashCode does not match StringState");
        }

        // Choose a hashcode to use for the supplied object.  The resulting
        // hashcode must fit in the payload in the MUW; in practice an address
        // can be used, but it may be worth revisiting this choice if using
        // a small nursery.

        internal static int ChooseHashCode(Object obj) {
            int result;
            if (obj is String) {
                // If the object is a string then this word holds its
                // StringState value instead.  We call ChooseHashCode
                // when getting an object hash code for the first time,
                // or when inflating it.  Only the latter applied for
                // String objects.
                result = 0;
            } else {
                // Hash code is int32. Unfortunately we cannot change that assumption.
                // The following cast will return only the lower bits in x64.
                // But it should not affect correctness.
                result = unchecked((int) (Magic.addressOf(obj) & HASHCODE_MASK));
            }
            DebugPrint("Chosen hash code {0:x} for {1:x}\n",
                       __arglist(result, Magic.addressOf(obj)));
            return result;
        }

#if !VC
        //----------------------------------------------------------------------
        //
        // STM
        //
        // The interaction between the STM and the multi-use-word is more complex
        // than that of GetMonitor and GetHashCode.
        //
        // The abstractions used are as follows:
        //
        //   - A STMHandle provides a reference to the MUW on a
        //     given object.  It provides all of the methods through which the
        //     STM implementation accesses the MUW.
        //
        //   - A STMSnapshot represents a saved view of the MUW at a given
        //     instant in time.  The snapshot is used when validating a
        //     transaction: if the current snapshot matches a saved snapshot
        //     then no update has been committed to the object in-between.
        //
        //   - A STMWord represents the meta-data that the STM itself wishes
        //     to maintain about the object.  Its structure is defined in
        //     TryAll.cs, but in outline, it either holds a version number for
        //     the object, or holds a pointer to an UpdateEnlistmentLog.Entry
        //     structure for the transaction that's currently got the object
        //     opened for update.
        //
        // When an object's MUW is used only for STM operations then the
        // STMSnapshot and the STMWord both come directly from the MUW.
        //
        // When an object has been used for one purpose other than the STM
        // then its STMWord is conceptually 0 (this is safe: it's not been
        // used by the STM so no updates have been committed to it).
        //
        // If an object has been inflated then the value in the MUW still
        // forms the STMSnapshot, but the STMWord is displaced to the
        // EMU.

        [NoLoggingForUndo]
        internal struct STMSnapshot {

            internal UIntPtr value;

            internal STMSnapshot (MultiUseWord muw) {
#if REFERENCE_COUNTING_GC || DEFERRED_REFERENCE_COUNTING_GC
                VTable.Assert(false, "STM not supported with RC collector");
#endif
                this.value = muw.value;
            }

            // Map from an STMSnapshot to an STMWord.  Ordinarily we
            // hope the object has an STM_TAG and the STMWord comes directly
            // from the snapshot.

            [Inline]
            internal STMWord GetSTMWord() {
                uint snapshotTag = (this.value & TAG_MASK);
                STMWord result;

                if (snapshotTag == STM_TAG) {
                    // STMWord is held in the MUW's payload
                    result = new STMWord(this.value);

                } else if (snapshotTag == INFLATED_TAG) {
                    // STMWord is held out-of-line in the EMU
                    UIntPtr payload = (this.value & PAYLOAD_MASK);
                    EMU emu = EMU.FromAddress(payload - PostHeader.Size);
                    result = emu.stmWord;

                } else {
                    // STMWord is conceptually zero: the object has a hashcode
                    // or Monitor, but has never been opened for update by the STM.
                    result = new STMWord(UIntPtr.Zero);
                }

                DebugPrint("Got word {0:x} from snapshot {1:x}\n",
                           __arglist(result.value, this.value));

                return result;
            }

            // Fast test of whether a snapshot is quiescent, on the assumption
            // that the snapshot is likely to be an STM word.

            [Inline]
            internal uint ZeroIfMustBeQuiescent() {
                VTable.Assert(STM_TAG == 0);
                return (this.value & (TAG_MASK | STMWord.IS_OWNED_MASK));
            }

            // Visit an STMSnapshot during GC.  We need to update any
            // pointer-derived values that it contains.  There are two
            // cases:
            //
            //  a. It refers to a Monitor or an EMU structure: extract the
            //     pointer, visit that, and then pack it back up with the
            //     appropriate tag.
            //
            //  b. It contains an STMWord: unpack that, then call the
            //     STM's method than knows how to deal with STMWords.

            internal unsafe void Visit(DirectReferenceVisitor v) {
                MultiUseWord muw = new MultiUseWord(this.value);
                DebugPrint("Visit STM snapshot {0:x}\n", __arglist(muw.value));
                uint tag = muw.GetTag();
                if (tag == MONITOR_TAG || tag == INFLATED_TAG) {
                    // Pointer-derived value managed by MultiUseWord.cs
                    UIntPtr payload = (UIntPtr) muw.GetPayload();
                    UIntPtr addr = (payload - PostHeader.Size);
                    v.Visit(&addr);
                    payload = (addr + PostHeader.Size);
                    muw = new MultiUseWord(tag, payload);
                }

                if (tag == STM_TAG) {
                    // Opaque value (possibly pointer-derived) managed by
                    // TryAll.cs
                    STMWord stmWord = GetSTMWord();
                    stmWord.Visit(v);
                    muw = new MultiUseWord(tag, stmWord.value);
                }

                DebugPrint("Visit STM snapshot, result = {0:x}\n",
                           __arglist(muw.value));
                this.value = muw.value;
            }

            internal bool Eq(STMSnapshot other) {
                return (this.value == other.value);
            }

            internal bool Neq(STMSnapshot other) {
                return (this.value != other.value);
            }
        }


        [NoLoggingForUndo]
        internal struct STMHandle {
            internal UIntPtr addr;

#if !DEBUG
            [Inline] [DisableBoundsChecks] [DisableNullChecks]
#endif
            internal unsafe STMHandle(Object obj) {
#if REFERENCE_COUNTING_GC || DEFERRED_REFERENCE_COUNTING_GC
                VTable.Assert(false, "STM not supported with RC collector");
#endif
                this.addr = Magic.addressOf(obj);
            }

#if !DEBUG
            [Inline] [DisableBoundsChecks] [DisableNullChecks]
#endif
            internal unsafe STMSnapshot GetSTMSnapshot() {
                Object obj = Magic.fromAddress(this.addr);
                return new STMSnapshot(GetForObject(obj));
            }

            internal unsafe void SetSTMWordAtAllocation(STMWord s) {
                VTable.Assert(GetSTMSnapshot().value == UIntPtr.Zero);
                VTable.Assert((s.value & TAG_MASK) == STM_TAG);
                Object obj = Magic.fromAddress(this.addr);
                SetForObject(obj, new MultiUseWord(s.value));
            }

            internal unsafe void SetSTMWordAtGC(DirectReferenceVisitor rv,
                                                STMWord s) {
                VTable.Assert((s.value & TAG_MASK) == STM_TAG);
                UIntPtr curSnapVal = GetSTMSnapshot().value;
                uint curTag = (curSnapVal & TAG_MASK);
                if (curTag == STM_TAG) {
                    Object obj = Magic.fromAddress(this.addr);
                    SetForObject(obj, new MultiUseWord(s.value));
                } else {
                    UIntPtr payload = (curSnapVal & PAYLOAD_MASK);
                    UIntPtr ptrVal = (payload - PostHeader.Size);
                    rv.Visit(&ptrVal);
                    EMU emu = EMU.FromAddress(ptrVal);
                    emu.stmWord.value = s.value;
                }
            }

            // Attempt to update the STMWord for the object that this handle
            // refers to.
            //
            // If the object has not been inflated then the STM word is held
            // directly in the MUW: try to update it with a compare and swap.
            //
            // If the object has been inflated then the STM word is held out-of-line
            // in the EMU.  Map from the supplied snapshot to the EMU, and then
            // do a compare and swap on the STMWord field that it contains.

            internal unsafe bool CompareExchangeSTMWord(UIntPtr newWord,
                                                        UIntPtr oldWord,
                                                        STMSnapshot oldSnapshot) {
                UIntPtr oldSnapVal = oldSnapshot.value;
                VTable.Assert((newWord & TAG_MASK) == 0);
                VTable.Assert((oldWord & TAG_MASK) == 0);
                uint oldTag = (oldSnapVal & TAG_MASK);
                bool result;

                VTable.Assert((newWord & MARK_BIT_MASK) == 0);
                VTable.Assert((oldWord & MARK_BIT_MASK) == 0);

                DebugPrint("CompareExchangeSTMWord on {0:x}, {1:x}/{2:x} -> {3:x}\n",
                           __arglist(this.addr, oldSnapVal, oldWord, newWord));

                if (oldTag == STM_TAG) {
                    VTable.Assert(oldWord == oldSnapshot.value);
                    Object obj = Magic.fromAddress(this.addr);
                    result = (CompareExchangeForObject(obj, newWord, oldWord)
                              == oldWord);
                } else {
                    if  (oldTag != INFLATED_TAG) {
                        DebugPrint("CompareExchangeSTMWord triggered inflation\n");
                        Object obj = Magic.fromAddress(this.addr);
                        Inflate(obj);
                        IncrementInflationToCount(STM_TAG);
                        oldSnapVal = GetForObject(obj).value;
                    }

                    EMU emu = new MultiUseWord(oldSnapVal).GetEMURefPayload();
                    result = (Interlocked.CompareExchange(ref emu.stmWord.value,
                                                          newWord,
                                                          oldWord) == oldWord);
                }
                return result;
            }

            internal unsafe void RefreshSTMWord(STMWord newWord) {
                DebugPrint("RefreshSTMValue on {0:x} to {1:x}\n",
                           __arglist(this.addr, newWord.value));

                Object obj = Magic.fromAddress(this.addr);
                UIntPtr curVal = GetForObject(obj).value;
                uint curTag = (curVal & TAG_MASK);
                VTable.Assert((curTag == STM_TAG) ||
                              (curTag == INFLATED_TAG));
                if (curTag == STM_TAG) {
                    VTable.Assert((newWord.value & TAG_MASK) == 0);
                    UIntPtr saw =
                        CompareExchangeForObject(obj, newWord.value, curVal);

                    // NB: we have the object opened for update, and so if our
                    // Interlocked.CompareExchange failed then it must be because another
                    // thread triggered inflation.
                    if (saw != curVal) {
                        VTable.Assert((saw & TAG_MASK) ==
                                      INFLATED_TAG);
                        ReInflate(obj, newWord);
                    }

                    if (Occasionally()) {
                        MultiUseWord m = GetForObject(obj);
                        if (!(m.IsInflated())) {
                            Inflate(obj);
                            IncrementInflationToCount(STM_TAG);
                        }
                    }
                } else {
                    ReInflate(obj, newWord);
                }
            }

            // Visit the object that the STMHandle refers to.  This is usually used
            // with a visitor that treats the reference as weak; we return false
            // if the visitor null's out the object reference.
            internal unsafe bool Visit(DirectReferenceVisitor v) {
                UIntPtr t = this.addr;
                v.Visit(&t);
                if (t == UIntPtr.Zero) {
                    return false;
                } else {
                    this.addr = t;
                    return true;
                }
            }

            internal unsafe bool IsMarked() {
                Object obj = Magic.fromAddress(this.addr);
                MultiUseWord muw = GetForObject(obj);
                return muw.IsMarked();
            }

            internal unsafe void SetMark(bool mark) {
                Object obj = Magic.fromAddress(this.addr);
                MultiUseWord muw = GetForObject(obj);
                MultiUseWord newMuw;
                if (mark) {
                    newMuw = new MultiUseWord(muw.value | (UIntPtr)MARK_BIT_MASK);
                } else {
                    newMuw = new MultiUseWord(muw.value & (UIntPtr)(~MARK_BIT_MASK));
                }
                SetForObject(obj, newMuw);
            }

            internal static void ReInflate(Object obj, STMWord newWord) {
                MultiUseWord saw;
                EMU curEMU;

                // Allocate new EMU first so that we do not have to consider
                // GC during the rest of this function.
                EMU newEMU = new EMU();
                IncrementReInflationCount();

                // Transfer current emu contents to the new EMU.
                saw = GetForObject(obj);
                VTable.Assert(saw.IsInflated());
                VTable.Assert(!saw.IsMarked());
                curEMU = saw.GetEMURefPayload();
                VTable.Assert(curEMU.Target == obj);
                newEMU.Target = obj;
                newEMU.Monitor = curEMU.Monitor;
                newEMU.HashCode = curEMU.HashCode;
                newEMU.stmWord = newWord;

                // Install new EMU in place of existing one
                curEMU.Target = null;
                SetForObject(obj, new MultiUseWord(INFLATED_TAG, newEMU));
                newEMU.Register();

                DebugPrint("ReInflation: EMU {0:x} becomes {1:x}\n",
                           __arglist(Magic.addressOf(curEMU),
                                     Magic.addressOf(newEMU)));

            }
        }
#endif

        //----------------------------------------------------------------------
        //
        // Cause the multi-use word on "obj" to be inflated.
        //
        // This method guarantees that obj is inflated before it returns:
        // however, it may be that the inflation itself is performed by a
        // second thread if multiple threads race to inflate the same object.
        //
        // For simplicity of code we allocate a Monitor for each inflated
        // object.  This will cause unnecessary monitor allocations in
        // applications where GetHashCode and STM operations are performed
        // on the same object (otherwise, at least one of the operations
        // requiring the MUW is a GetMonitor call).
        //
        // Why can't we just leave the Monitor field NULL and allocate the
        // Monitor lazily?  The problem is how to avoid a race with the
        // STM which must do the same thing with its field in the EMU
        // object -- suppose thread A is about to re-inflate an object
        // just when thread B is about to install a Monitor in the EMU.
        // The monitor would be lost.
        //
        // If the extra Monitor allocations are a problem then we could
        // use a more complicated handshaking scheme whereby a thread that
        // is reinflating an object must install a distinct value in the
        // EMU's monitor field.

        internal static void Inflate(Object obj) {

            MultiUseWord saw = GetForObject(obj);
            while (!saw.IsInflated()) {
                VTable.Assert(!saw.IsInflated());
                VTable.Assert(!saw.IsMarked());

                // Remember: extract any reference-typed payload from "saw"
                // before we do anything that might trigger a GC.

                uint sawTag = saw.GetTag();
                int hashCode = (sawTag == HASHCODE_TAG)
                    ? (int)(saw.GetPayload()) : ChooseHashCode(obj);
                Monitor monitor = (sawTag == MONITOR_TAG)
                    ? (Monitor)(saw.GetRefPayload()) : new Monitor();
                EMU emu = new EMU();
                IncrementFullEMUAllocCount();

#if REFERENCE_COUNTING_GC || DEFERRED_REFERENCE_COUNTING_GC
                if (sawTag != MONITOR_TAG) {
                    DebugPrint("+rc on monitor {0:x}\n",
                               __arglist(Magic.addressOf(monitor)));
                    NonNullIncrementRefCount(monitor);
                }
                DebugPrint("+rc on emu {0:x}\n", __arglist(Magic.addressOf(emu)));
                NonNullIncrementRefCount(emu);
#endif

                emu.Target = obj;
                emu.Monitor = monitor;
                emu.HashCode = hashCode;
#if !VC
                emu.stmWord = ((saw.value & TAG_MASK) == STM_TAG)
                    ? new STMWord(saw.value) : new STMWord(UIntPtr.Zero);
#endif

                MultiUseWord newWord = new MultiUseWord(INFLATED_TAG,emu);
                DebugPrint("Inflating {0:x} from {1:x} to {2:x} with hashcode {3:x}\n",
                           __arglist(Magic.addressOf(obj),
                                     saw.value,
                                     newWord.value,
                                     emu.HashCode));
                MultiUseWord now = CompareExchangeForObject(obj,
                                                            newWord,
                                                            saw);
                if (now.Eq(saw)) {
                    // Inflation successful
#if REFERENCE_COUNTING_GC || DEFERRED_REFERENCE_COUNTING_GC
                    RegisterLostObjForVerifyHeap(obj, emu);
#else
                    emu.Register();
#endif
                    IncrementInflationFromCount(saw.GetTag());
                    break;
                } else {
                    // Inflation not successful
#if REFERENCE_COUNTING_GC || DEFERRED_REFERENCE_COUNTING_GC
                    if (sawTag != MONITOR_TAG) {
                        DebugPrint("-rc on monitor {0:x}\n",
                                   __arglist(Magic.addressOf(monitor)));
                        NonNullDecrementRefCount(monitor);
                    }
                    DebugPrint("-rc on emu {0:x}\n",
                               __arglist(Magic.addressOf(emu)));
                    NonNullDecrementRefCount(emu);
#endif
                    IncrementAbandonedEMUsCount();
                }

                saw = now;
            }
        }

        //----------------------------------------------------------------------
        //
        // GC support (reference counting collector)
        //
        // NB: STM is not supported with the reference counting collector.  This
        // is a limitation in TryAll.cs, not specifically here.
        //
        // The Monitor and EMU objects allocated here are managed as follows:
        //
        //  - The compiler automatically inserts RC modifications when
        //    casting the MUW's payload to a reference type (either a Monitor or
        //    an EMU).
        //
        //  - We manually increment and decrement the count on a Monitor or
        //    EMU object while it is reachable from the multi-use word.
        //    That is, we increment the count just before making it reachable
        //    from the word, and we decrement the count (a) when the object
        //    it's associated has count of 0, or (b) when we inflate a Monitor
        //    with an EMU.
        //
        //  - The Monitor and EMU objects are _not_ threaded on a list as they
        //    are with tracing collectors.  The tracing collectors need the
        //    list so they can visit the Monitor and EMU objects that are alive
        //    only because of references from multi-use words (the alternative
        //    is for the GC to visit all MultiUseWords, but we anticipate most
        //    holding scalars).
        //
        // The RC collector is responsible for calling RefCountGCDeadObjHook (below)
        // on each object that has a 0 count.  Since we're called from within
        // the RC collector we use ManualRefCounts and tread carefully when
        // dealing with pointer-derived values -- i.e. directly extracting
        // them without automatic RC updates rather than going through the usual
        // accessors.

        [ManualRefCounts]
        internal static void RefCountGCDeadObjHook(MultiUseWord muw) {
#if REFERENCE_COUNTING_GC || DEFERRED_REFERENCE_COUNTING_GC
            uint tag = muw.GetTag();
            VTable.Assert(tag == MONITOR_TAG || tag == INFLATED_TAG,
                          "tag == MONITOR_TAG || tag == INFLATED_TAG");

            UIntPtr payload = (UIntPtr) muw.GetPayload();
            Object refPayload = Magic.fromAddress(payload - PostHeader.Size);
            if (tag == MONITOR_TAG) {
                Monitor m = Magic.toMonitor(refPayload);
                DebugPrint("-rc on monitor on dead obj {0:x}\n",
                           __arglist(Magic.addressOf(m)));
                NonNullDecrementRefCount(m);
            } else {
                EMU emu = Magic.toEMU(refPayload);
                Monitor m =
                    Magic.toMonitor(Magic.fromAddress(emu.monitor));
                DebugPrint("-rc on monitor on dead obj {0:x}\n",
                           __arglist(Magic.addressOf(m)));
                NonNullDecrementRefCount(m);
                DebugPrint("-rc on emu on dead obj {0:x}\n",
                            __arglist(Magic.addressOf(emu)));
                NonNullDecrementRefCount(emu);
            }
#endif
        }

        //----------------------------------------------------------------------
        //
        // GC support (tracing collectors)
        //
        // We must co-operate with the GC in order to (a) ensure that active EMU
        // objects and the Monitors reachable from them are treated as reachable,
        // (b) allow EMU to be reclaimed when their target is NULL or when their
        // target has died, and (c) update object header words if a collector
        // moves an EMU object.
        //
        // The implementation must be careful to work with all three tracing
        // collectors because of the different ways in which they process the
        // heap during collection (mark-sweep, semispace, sliding).  In overview:
        //
        //    Mark-sweep : This is the easy case.  Objects are not moved and
        //                 their fields remain traversable during collection.
        //                 A bit in the vtable word is used as a mark bit and
        //                 so we cannot make ordinary method calls on an object
        //                 if it may be marked, and we cannot perform other
        //                 operations that use the vtable (e.g. checked casts).
        //
        //    Semispace :  Objects are moved during collection, with the vtable
        //                 word holding a forwarding pointer.  As above, we must
        //                 avoid operations that may require the vtable.  Furthermore,
        //                 if we are going to update an object during GC, we must
        //                 make sure that we update the to-space version and not
        //                 the from-space version.  We deal with that by ensuring
        //                 that all objects accessed have already been visited.
        //
        //    Sliding:     This is a mark-compact collector.  During the mark phase
        //                 an object's vtable word forms the head of a list of
        //                 references that will need to be updated.  This list
        //                 is threaded through the object references themselves,
        //                 so we cannot traverse object-typed fields once an
        //                 object's fields have been visited.  We avoid this by
        //                 building our own shadow list of EMU objects: we do not
        //                 visit the emuGCListShadow and nextShadow fields which
        //                 make up this list.
        //
        // We receive callbacks from these tracing collectors at four times:
        //
        // 1. PreGCHook is called with the world stopped but before any marking
        //    is done on the EMU objects.  At this point we collect recently
        //    allocated EMU objects from per-thread lists onto a global list at
        //    emuGCList.  If we're using the sliding collector then we build a
        //    duplicate shadow list.
        //    When onlyNew parameter is true, we only scan recently allocated
        //    EMU objects from per-thread list between GC.
        //    When onlyNew parameter is false, we scan all the EMU objects
        //    (newly allocated EMU + EMU that live after previous GC --
        //    emuGCListAll..emuGCListAllTail)
        //
        // 2. VisitStrongRefs is called during the mark phase (for mark-sweep
        //    and sliding collectors) or during copying (for semispace).  It is
        //    responsible for visiting the EMU objects and sometimes the Monitor
        //    objects reachable from them.  The references to these are strong:
        //    unneeded EMUs are unlinked from emuGCList at the end of a GC cycle
        //    and reclaimed in the next.
        //
        //    Monitor objects can be reclaimed if they are not in use (that is,
        //    they are not held nor being waited on by any objects).  In this
        //    case, they are treated as weak references.  If a thread has a
        //    local reference to an object's monitor and is about to enter when
        //    a GC occurs, then reclaiming the monitor will result in a lock
        //    on a disconnected monitor.  This only current works for
        //    stop-the-world collectors as we would effectively need a read
        //    barrier on the monitor field to avoid the locking/reclaiming
        //    race - so collectors marked IsOnTheFlyCollector will always
        //    treat the references to monitors as strong.

        //
        //    NB: during VisitStrongRefs we cannot assume that the EMUs have not
        //    already been visited.  This may happen if e.g. they lie on the same
        //    page as a pinned object.  This is why we use a visit-before-use
        //    access pattern.
        //
        // 3. VisitWeakRefs is called after the mark phase (for mark-sweep and
        //    sliding collectors) or after copying (for semispace).  It is no
        //    longer possible to mark further objects, but it is possible to
        //    inspect the mark bits via the weak ptr visitor that's passed in.
        //    During this phase we find all of the EMUs whose targets have
        //    died.  We record this by nulling out the EMU's target field.
        //
        // 4. PostGCHook is called just before restarting the world.  It can
        //    traverse the heap normally again.  It is responsible for updating
        //    the MUWs in the objects headers to refer to the new location of
        //    the EMU or Monitor.
        //    At the end of PostGCHook, we update emuGCListAll so it has all
        //    the surviving EMU objects.  We also clear emuGCList.
        //
        // Because of the collectors' use of the vtable word, we are careful to
        // (a) avoid casts during VisitStrongRefs and VisitWeakRefs (hence
        // EMU.FromAddress, rather than Magic.fromAddress + cast), and
        // (b) avoid virtual method calls during VisitStrongRefs and VisitWeakRefs
        // (hence EMU.ToAddress is a static method).

        // TODO: Documentation above does not discuss concurrent collector.
        // Are there race conditions involving thread termination and collection
        // on emuGCList?

        private static UIntPtr emuGCList;
        private static UIntPtr emuGCListShadow;
        private static UIntPtr emuGCListAll;
        private static UIntPtr emuGCListAllTail;

        // Collect EMUs that survived previous collections (unless 'onlyNew'
        // is set).
        internal static void CollectFromPreviousCollections(bool onlyNew) {
            if (onlyNew) {
                // emuGCListAll has entries that we don't want to scan.  We will
                // add the surviving entries to that list at the end of
                // PostGCHook.
                //
                // emuGCListAll and emuGCListAllTail are both valid for the list
                // of older items.
            } else {
                // We will prepend emuGCListAll to what we already have in
                // emuGCList (from thread termination) and then scan all of the
                // entries.

                if(emuGCListAllTail != UIntPtr.Zero) {
                    EMU.FromAddress(emuGCListAllTail).next = emuGCList;
                    emuGCList = emuGCListAll;
                }

                // emuGCListAll and emuGCListAllTail are now bogus and will be
                // replaced at the end of PostGCHook.
            }
        }

        // Called from 'thread', or with the world stopped.  Collects
        // EMUs allocated by the thread onto the global list.
        internal unsafe static void CollectFromThread(Thread thread) {
            if (thread.externalMultiUseObjAllocListHead != UIntPtr.Zero) {
                DebugPrint("CollectFromThread: thread {0:x}\n",
                           __arglist(Magic.addressOf(thread)));
                EMU firstEmu =
                    EMU.FromAddress(thread.externalMultiUseObjAllocListHead);
                EMU lastEmu =
                    EMU.FromAddress(thread.externalMultiUseObjAllocListTail);
                DebugPrint("CollectFromThread: got {0:x}..{1:x}\n",
                           __arglist(Magic.addressOf(firstEmu),
                                     Magic.addressOf(lastEmu)));

                while (true) {
                    UIntPtr currentFirst = emuGCList;
                    lastEmu.next = currentFirst;

                    // Splice per-thread list onto the global list.  NB: in
                    // most cases this can be a direct assignment, but in principle
                    // a CAS is needed to deal with a race where two threads
                    // finish concurrently.

                    if (Interlocked.CompareExchange(ref emuGCList,
                                                    Magic.addressOf(firstEmu),
                                                    currentFirst) == currentFirst) {
                        DebugPrint("CollectFromThread: installed\n");
                        thread.externalMultiUseObjAllocListHead = UIntPtr.Zero;
                        thread.externalMultiUseObjAllocListTail = UIntPtr.Zero;
                        break;
                    } else {
                        DebugPrint("CollectFromThread: race, retrying install\n");
                    }
                }
            }
        }

        // Collect recently allocated EMUs from per-thread lists onto
        // the global EMU list hanging off emuGCList.
        private static void CollectFromThreads(bool onlyNew) {
            Thread[] threadTable = Thread.threadTable;
            int limit = threadTable.Length;
            for (int i = 0; i < limit; i++) {
                Thread thread = threadTable[i];
                if (thread != null) {
                    CollectFromThread(thread);
                }
            }
        }

        // Called with the world stopped, before marking begins.  Responsible
        // for updating our list of all EMU objects.
        internal unsafe static void PreGCHook(bool useShadows) {
            PreGCHook(useShadows, false);
        }

        internal unsafe static void PreGCHook(bool useShadows, bool onlyNew) {
            DebugPrint("GC: PrepareCollectEMUs\n");

            // Collect EMUs that survived previous collections (unless 'onlyNew'
            // is set).
            CollectFromPreviousCollections(onlyNew);

            // Collect recently allocated EMUs from per-thread lists onto
            // the global EMU list hanging off emuGCList.
            CollectFromThreads(onlyNew);

            if (useShadows) {
                // Build shadow lists if necessary.  These will not be visited during
                // GC: they're needed for the sliding collector which updates
                // fields that are visited during the mark phase.
                emuGCListShadow = emuGCList;
                EMU i = EMU.FromAddress(emuGCListShadow);
                while (i != null) {
                    i.NextShadow = i.Next;
                    i = i.Next;
                }
            }
            // count the number of emu in the list.
            ComputeEmuCount(useShadows);
        }

        // Called during the mark phase.  Responsible for keeping alive the
        // EMU objects and the Monitors reachable from them.
        internal unsafe static
        void VisitStrongRefs(DirectReferenceVisitor strongReferenceVisitor,
                             bool useShadows)
        {
            DebugPrint("GC: VisitStrongRefs\n");

#if REFERENCE_COUNTING_GC || DEFERRED_REFERENCE_COUNTING_GC
            VisitStrongRefsRC(strongReferenceVisitor);
#else
            VisitStrongRefsNonRC(strongReferenceVisitor, useShadows);
#endif
        }


        // With the RC collector VisitStrongRefs is only called during VerifyHeap
        // when traversing the heap to find the objects that are reachable.  We
        // need to visit any Monitor and EMU objects that are kept alive via
        // MUWs.
        //
        // Because this is not fast-path code, we just visit every object in the
        // heap and visit reference-derived values in the MUW field, and (for inflated
        // objects) in the Monitor field of the EMU.  We keep a separate list of
        // Monitor and EMU objects that have been retained from objects in
        // non-GC pages (e.g. from locking on RuntimeType objects).

#if REFERENCE_COUNTING_GC || DEFERRED_REFERENCE_COUNTING_GC
        internal unsafe static
        void VisitStrongRefsRC(DirectReferenceVisitor strongRefVisitor)
        {
            VTable.Assert(VerificationMode, @"VerificationMode");

            DebugPrint("GC: VisitStrongRefsRC");

            VTable.Assert(emuGCList == UIntPtr.Zero);

            Visitor.Initialize(strongRefVisitor);
            SegregatedFreeList.VisitAllObjects(Visitor);
        }

        private static MUWVisitor Visitor = new MUWVisitor();

        private class MUWVisitor : SegregatedFreeList.ObjectVisitor {

            private DirectReferenceVisitor Visitor;

            [ManualRefCounts]
            internal override void VisitSmall(Object obj, UIntPtr memAddr) {
                this.Visit(obj);
            }

            [ManualRefCounts]
            internal override UIntPtr VisitLarge(Object obj) {
                return this.Visit(obj);
            }

            [ManualRefCounts]
            internal override unsafe UIntPtr Visit(Object obj) {
                MultiUseWord muw = GetForObject(obj);
                uint tag = muw.GetTag();
                if (tag == MONITOR_TAG || tag == INFLATED_TAG) {
                    UIntPtr payload = (UIntPtr) muw.GetPayload();
                    UIntPtr addr = (payload - PostHeader.Size);
                    DebugPrint("GC: VisitStrongRefsRC visiting {0:x}\n",
                               __arglist(addr));
                    this.Visitor.Visit(&addr);
                    if (tag == INFLATED_TAG) {
                        EMU emu = EMU.FromAddress(muw.GetPayload() - PostHeader.Size);
                        UIntPtr m = emu.monitor;
                        DebugPrint("GC: VisitStrongRefsRC visiting {0:x}\n",
                                   __arglist(m));
                        this.Visitor.Visit(&m);
                    }
                }
                VTable vtable = obj.vtable;
                return ObjectLayout.ObjectSize(Magic.addressOf(obj), vtable);
            }

            [ManualRefCounts]
            internal void Initialize(DirectReferenceVisitor visitor) {
                this.Visitor = visitor;
            }
        }

        private static void RegisterLostObjForVerifyHeap(Object owner,
                                                         Object obj) {
            if (VerificationMode) {
                UIntPtr page = PageTable.Page(Magic.addressOf(owner));
                PageType pageType = PageTable.Type(page);
                if (PageTable.IsNonGcPage(pageType)) {
                    DebugPrint("GC: Registering permanent object {0:x} -> {1:x}\n",
                               __arglist(Magic.addressOf(owner),
                                         Magic.addressOf(obj)));
                    PermanentObj po = new PermanentObj();
                    po.Obj = obj;
                    po.Next = PermanentObjList;
                    PermanentObjList = po;
                }
            }
        }

        private static PermanentObj PermanentObjList;

        private class PermanentObj {
            internal Object Obj;
            internal PermanentObj Next;
        }
#endif

#if REFERENCE_COUNTING_GC
        [ManualRefCounts]
        internal static void NonNullIncrementRefCount(Object obj) {
            ReferenceCountingCollector.
            NonNullIncrementRefCount(obj);
        }

        [ManualRefCounts]
        internal static void NonNullDecrementRefCount(Object obj) {
            ReferenceCountingCollector.
            NonNullDecrementRefCount(obj);
        }

        internal static bool VerificationMode {
            [ManualRefCounts]
            get {
                return ReferenceCountingCollector.VerificationMode;
            }
        }
#endif

#if DEFERRED_REFERENCE_COUNTING_GC
        [ManualRefCounts]
        internal static void NonNullIncrementRefCount(Object obj) {
            DeferredReferenceCountingCollector.
            NonNullIncrementRefCount(obj);
        }

        [ManualRefCounts]
        internal static void NonNullDecrementRefCount(Object obj) {
            DeferredReferenceCountingCollector.
            NonNullDecrementRefCount(obj);
        }

        internal static bool VerificationMode {
            [ManualRefCounts]
            get {
                return DeferredReferenceCountingCollector.VerificationMode;
            }
        }
#endif


        // With a tracing collector we visit Monitor and EMU objects by linking
        // them on emuGCList.  This avoids us needing to visit MUWs on all objects
        // in the heap on every GC.

#if !(REFERENCE_COUNTING_GC || DEFERRED_REFERENCE_COUNTING_GC)
        internal unsafe static
        void VisitStrongRefsNonRC(DirectReferenceVisitor strongRefVisitor,
                                  bool useShadows)
        {
            DebugPrint("GC: VisitStrongRefsNonRC\n");
            
            fixed (UIntPtr *loc = &emuGCList) {
                if (*loc != UIntPtr.Zero) {
                    strongRefVisitor.Visit(loc);
                }
            }

            EMU emu = EMU.FromAddress(useShadows ? emuGCListShadow : emuGCList);
            while (emu != null) {
                // Visit the EMU's monitor field

                if (emu.monitor != UIntPtr.Zero) {

                    Monitor m = Monitor.FromAddress(emu.monitor);

                    if (!GC.installedGC.IsOnTheFlyCollector
                        && m != null && !m.IsInUse() && emu.IsMonitor()) {
                        // Do nothing.  The monitor will be treated as a
                        // weak reference instead.
                    } else {
                        DebugPrint
                            ("GC: Visiting {0:x}'s monitor field {1:x}\n",
                             __arglist(Magic.addressOf(emu), emu.monitor));
                        fixed (UIntPtr* loc = &emu.monitor) {
                            strongRefVisitor.Visit(loc);
                        }
                        DebugPrint("GC: Now {0:x}\n",
                                   __arglist(emu.monitor));
                    }
                }

#if !VC
                // Visit the EMU's STM word
                DebugPrint("GC: Visiting {0:x}'s STM word {1:x}\n",
                           __arglist(Magic.addressOf(emu), emu.stmWord.value));
                STMWord w = emu.stmWord;
                w.Visit(strongRefVisitor);
                emu.stmWord = w;
                DebugPrint("GC: Now {0:x}\n",
                           __arglist(emu.stmWord.value));
#endif

                // Visit the EMU's next field
                DebugPrint("GC: Visiting {0:x}'s next field {1:x}\n",
                           __arglist(Magic.addressOf(emu), emu.next));
                fixed (UIntPtr *loc = &emu.next) {
                    if (*loc != UIntPtr.Zero) {
                        strongRefVisitor.Visit(loc);
                    }
                }
                DebugPrint("GC: Now {0:x}\n",
                           __arglist(emu.next));

                emu = useShadows ? emu.NextShadow : emu.Next;
            }

            DebugPrint("GC: VisitStrongRefsNonRC done\n");
        }
#endif

        // Called after the mark phase.  Responsible for identifying EMU objects
        // whose targets have become dead.  This is indicated by the
        // weakReferenceVisitor nulling out the target field.  Any such EMUs
        // are then cut out of the global list in PostGCHook.
        internal unsafe static
        void VisitWeakRefs(DirectReferenceVisitor weakReferenceVisitor,
                           bool useShadows)
        {
            DebugPrint("GC: VisitWeakRefs\n");

            EMU emu = EMU.FromAddress(useShadows ? emuGCListShadow : emuGCList);
            while (emu != null) {
                if (emu.monitor != UIntPtr.Zero) {

                    Monitor m = Monitor.FromAddress(emu.monitor);

                    if (!GC.installedGC.IsOnTheFlyCollector
                        && m != null && !m.IsInUse() && emu.IsMonitor()) {
                        DebugPrint
                            ("GC: Visiting {0:x}'s monitor field {1:x}\n",
                             __arglist(Magic.addressOf(emu), emu.monitor));
                        fixed (UIntPtr *loc = &emu.monitor) {
                            weakReferenceVisitor.Visit(loc);
                        }
                        DebugPrint("GC: Now {0:x}\n", __arglist(emu.monitor));
                    }
                }

                DebugPrint("GC: Visiting {0:x}'s target field {1:x}\n",
                           __arglist(Magic.addressOf(emu), emu.target));

                fixed (UIntPtr *loc = &emu.target) {
                    if (*loc != UIntPtr.Zero) {
                        weakReferenceVisitor.Visit(loc);
                    }
                }
                DebugPrint("GC: Now {0:x}\n", __arglist(emu.target));
                emu = useShadows ? emu.NextShadow : emu.Next;
            }
        }

        // Called just before starting the world.  Responsible for excising
        // unneeded EMUs from the global list and for updating the MUW header
        // in objects whose EMU or Monitor may have moved.
        internal unsafe static void PostGCHook() {
            PostGCHook(false);
        }

        internal unsafe static void PostGCHook(bool onlyNew) {
            DebugPrint("GC: PostGCHook\n");

            EMU emu = EMU.FromAddress(emuGCList);

            // We traverse emuGCList with prevLivingEMU pointing to the
            // most recent entry that should be kept in the list.
            EMU prevLivingEMU = null;
            bool inDeadRun = false;

            while (emu != null) {
                bool live = false;

                if (emu.target != UIntPtr.Zero) {
                    // Either (a) the EMU really is still needed, or (b) the
                    // EMU was allocated when a Monitor was provided for the
                    // object and it's been replaced by a full EMU.
                    // or (c) the emu was only a monitor which has been removed
                    // and emu needs to be removed also

                    MultiUseWord muw = GetForObject(emu.Target);
                    DebugPrint("GC: {0:x} target non-null {1:x}, tag {2:x}\n",
                               __arglist(Magic.addressOf(emu),
                                         emu.target,
                                         muw.GetTag()));

                    VTable.Assert(muw.IsInflated() || muw.IsMonitor());

                    if (muw.IsMonitor()) {
                        // MONITOR_TAG on the object: keep the EMU (it must be
                        // a monitor EMU).
                        VTable.Assert(emu.IsMonitor());

                        // This monitor was unused, thus set to zero when visiting
                        // Set the muw in object to unused and remove emu

                        if (emu.monitor == UIntPtr.Zero)
                        {
                            MultiUseWord muwTemp = new MultiUseWord(UIntPtr.Zero);
                            SetForObject(emu.Target, muwTemp);
                            emu.target = UIntPtr.Zero;
                        } else {
                            muw = new MultiUseWord(MONITOR_TAG, emu.Monitor);
                            SetForObject(emu.Target, muw);
                            live = true;
                        }

                    } else {
                        // INFLATED_TAG on the object: only keep the EMU
                        // if it's a full EMU.
                        if (!emu.IsMonitor()) {
                            muw = new MultiUseWord(INFLATED_TAG, emu);
                            SetForObject(emu.Target, muw);
                            live = true;
                        }
                    }
                }

                if (live) {
                    // If this EMU is still needed then cut out any
                    // run of dead predecessors in the list.

                    DebugPrint("GC: {0:x} is alive\n", __arglist(EMU.ToAddress(emu)));
                    if (inDeadRun) {
                        DebugPrint("GC: {0:x} is new successor of {1:x}\n",
                                   __arglist(Magic.addressOf(emu),
                                             Magic.addressOf(prevLivingEMU)));
                        if (prevLivingEMU == null) {
                            emuGCList = Magic.addressOf(emu);
                        } else {
                            prevLivingEMU.next = Magic.addressOf(emu);
                        }
                        inDeadRun = false;
                    }
                    prevLivingEMU = emu;
                } else {
                    // EMU is not needed.  Either (a) the target was nulled
                    // out by weakReferenceVisitor, or (b) a new EMU was
                    // allocated for this target and target was nulled out at
                    // that point.  In either case we should cut it from the
                    // list and let it be collected at the next GC.

                    DebugPrint("GC: {0:x} is dead\n",
                               __arglist(EMU.ToAddress(emu)));
                    IncrementDeadEMUsCount();
                    inDeadRun = true;
                }

                emu = emu.Next;
            }

            if (inDeadRun) {
                DebugPrint("GC: {0:x} is new tail\n",
                           __arglist(Magic.addressOf(prevLivingEMU)));
                if (prevLivingEMU == null) {
                    emuGCList = UIntPtr.Zero;
                } else {
                    prevLivingEMU.next = UIntPtr.Zero;
                }
            }

            if (onlyNew) {
                // Prepend surviving entries to the list already contained in
                // emuGCListAll...emuGCListAllTail.
                if (prevLivingEMU != null) {
                    prevLivingEMU.next = emuGCListAll;
                    emuGCListAll = emuGCList;
                    if (emuGCListAllTail == UIntPtr.Zero) {
                        emuGCListAllTail = Magic.addressOf(prevLivingEMU);
                    }
                }
            } else {
                // Replace emuGCListAll with emuGCList because we copied the
                // "All" list into the list that we just processed.
                emuGCListAll = emuGCList;
                emuGCListAllTail = Magic.addressOf(prevLivingEMU);
            }

            // The emuGCList entries are contained in emuGCListAll, so now clear
            // emuGCList so that it can start receiving thread termination lists
            // for the next GC.
            emuGCList = UIntPtr.Zero;
        }

        //----------------------------------------------------------------------
        //
        // Debugging and tracing

        [System.Diagnostics.Conditional("ENABLE_LOG_TRACING")]
        [NoInline]
        internal static void DebugPrint(String v, __arglist)
        {
            VTable.DebugPrint(v, new ArgIterator(__arglist));
        }

        [System.Diagnostics.Conditional("ENABLE_LOG_TRACING")]
        [NoInline]
        internal static void DebugPrint(String v)
        {
            VTable.DebugPrint(v);
        }

        private static int[] InflationFromCount = new int[TAG_MASK + 1];
        private static int[] InflationToCount = new int[TAG_MASK + 1];
        private static int AbandonedEMUsCount = 0;
        private static int DeadEMUsCount = 0;
        private static int MonitorEMUAllocCount = 0;
        private static int FullEMUAllocCount = 0;
        private static int ReInflationCount = 0;

        [System.Diagnostics.Conditional("ENABLE_PROFILING")]
        internal static void IncrementInflationFromCount(uint tag)
        {
            VTable.Assert(tag >= 0 && tag <= TAG_MASK);
            InflationFromCount[tag] ++;
        }

        [System.Diagnostics.Conditional("ENABLE_PROFILING")]
        internal static void IncrementInflationToCount(uint tag)
        {
            VTable.Assert(tag >= 0 && tag <= TAG_MASK);
            InflationToCount[tag] ++;
        }

        [System.Diagnostics.Conditional("ENABLE_PROFILING")]
        internal static void IncrementReInflationCount()
        {
            ReInflationCount ++;
        }

        [System.Diagnostics.Conditional("ENABLE_PROFILING")]
        internal static void IncrementAbandonedEMUsCount()
        {
            AbandonedEMUsCount ++;
        }

        [System.Diagnostics.Conditional("ENABLE_PROFILING")]
        internal static void IncrementDeadEMUsCount()
        {
            DeadEMUsCount ++;
        }

        [System.Diagnostics.Conditional("ENABLE_PROFILING")]
        internal static void IncrementFullEMUAllocCount()
        {
            FullEMUAllocCount ++;
        }

        [System.Diagnostics.Conditional("ENABLE_PROFILING")]
        internal static void IncrementMonitorEMUAllocCount()
        {
            MonitorEMUAllocCount ++;
        }

        [System.Diagnostics.Conditional("ENABLE_PROFILING")]
        internal static void ComputeEmuCount(bool useShadows)
        {
            int total = 0;
            EMU emu = EMU.FromAddress(useShadows ? emuGCListShadow : emuGCList);
            while (emu != null) {
                total++;
                emu = useShadows ? emu.NextShadow : emu.Next;
            }
            Trace.Log(Trace.Area.Emu, "total {0} emu", __arglist(total));
        }


        internal static void DumpTables()
        {
#if ENABLE_PROFILING
            int monitorEMUs = 0;
            int fullEMUs = 0;
            int retargetedEMUs = 0;

            // Collect recently allocated EMUs from per-thread lists onto
            // the global EMU list hanging off emuGCList.
            CollectFromThreads(false);

            // Count EMUs on the global list
            EMU i = EMU.FromAddress(emuGCList);
            while (i != null) {
                if (i.Target == null) {
                    retargetedEMUs ++;
                } else {
                    MultiUseWord muw = GetForObject(i.Target);
                    if (muw.IsMonitor()) {
                        monitorEMUs ++;
                    } else {
                        VTable.Assert(muw.IsInflated());
                        fullEMUs ++;
                    }
                }
                i = i.Next;
            }

            // Output stats
            VTable.DebugPrint(@"
MultiUseWord stats: (non-thread-safe counters)
Full EMUs allocated:          {0}
Monitor EMUs allocated:       {1}
Reinflated EMUs allocated:    {2}
Total EMUs allocated:         {3}
",
__arglist(
          FullEMUAllocCount, // 0
          MonitorEMUAllocCount, // 1
          ReInflationCount, // 2
          FullEMUAllocCount + MonitorEMUAllocCount + ReInflationCount // 3
          ));

#if !(REFERENCE_COUNTING_GC || DEFERRED_REFERENCE_COUNTING_GC)
            VTable.DebugPrint(@"
Of which:
  EMUs abandoned at birth:    {0}
  EMUs found dead:            {1}
  Moribund reinflated EMUs:   {2}
  Live monitor EMUs:          {3}
  Live full EMUs:             {4}
  Total EMUs found :          {5}
",
__arglist(AbandonedEMUsCount, // 0
          DeadEMUsCount, // 1
          retargetedEMUs, // 2
          monitorEMUs, // 3
          fullEMUs, // 4
          (AbandonedEMUsCount +
           DeadEMUsCount +
           retargetedEMUs +
           monitorEMUs +
           fullEMUs) //5
          ));
#endif

            VTable.DebugPrint(@"
Inflation from STM:           {0}
          from hashcode:      {1}
          from monitor:       {2}
Inflation caused by STM:      {3}
          caused by hashcode: {4}
          caused by monitor:  {5}
",
__arglist(InflationFromCount[STM_TAG], // 0
          InflationFromCount[HASHCODE_TAG], // 1
          InflationFromCount[MONITOR_TAG], // 2
          InflationToCount[STM_TAG], // 3
          InflationToCount[HASHCODE_TAG], // 4
          InflationToCount[MONITOR_TAG] // 5
          ));
#endif
        }
    }

    // Because EMUs are encoded in the MultiUseWord payload, they must be 8-byte aligned
    [StructAlign(8)]
    internal class EMU {
        // Scalar fields holding scalar values
        internal int hashCode;
#if !VC
        internal STMWord stmWord;
#endif

        // Scalar fields holding references (accessed through properties below)
        internal UIntPtr target;
        internal UIntPtr monitor;
        internal UIntPtr next;
        internal UIntPtr nextShadow;

        public bool IsMonitor() {
            return (HashCode == 0);
        }

        //----------------------------------------------------------------------
        //
        // Scalar properties

        public int HashCode {
            get {
                return hashCode;
            }
            set {
                hashCode = value;
            }
        }

        //----------------------------------------------------------------------
        //
        // Accessor methods for scalar fields holding references

        public Object Target {
            get {
                return Barrier.WeakRefRead(target, 0);
            }
            set {
                target = Barrier.WeakRefWrite(value, 0);
            }
        }

        // FIXME: this other stuff could use some barriers!!

        public Monitor Monitor {
            get {
                return (Monitor)(Magic.fromAddress(this.monitor));
            }
            set {
                monitor = Magic.addressOf(value);
            }
        }

        public EMU Next {
            get {
                return FromAddress(this.next);
            }
            set {
                next = Magic.addressOf(value);
            }
        }
        
        public EMU NextShadow {
            get {
                return FromAddress(this.nextShadow);
            }
            set {
                nextShadow = Magic.addressOf(value);
            }
        }
        
        internal void Register() {
            Thread thread = Thread.CurrentThread;
            if (thread.externalMultiUseObjAllocListHead == UIntPtr.Zero) {
                VTable.Assert(thread.externalMultiUseObjAllocListTail == UIntPtr.Zero);
                thread.externalMultiUseObjAllocListHead = Magic.addressOf(this);
                thread.externalMultiUseObjAllocListTail = Magic.addressOf(this);
            } else {
                VTable.Assert(thread.externalMultiUseObjAllocListTail != UIntPtr.Zero);
                this.next = thread.externalMultiUseObjAllocListHead;
                thread.externalMultiUseObjAllocListHead = Magic.addressOf(this);
            }
        }


        //----------------------------------------------------------------------
        //
        // Type conversion methods.  Note: (1) we cannot do a checked cast
        // from Object to EMU during GC (because the GC may be using the
        // vtable word), (2) we don't make ToAddress an ordinary method in
        // case it's not compiled with devirtualization and the call goes
        // through the vtable.

        internal static EMU FromAddress(UIntPtr v) {
            return Magic.toEMU(Magic.fromAddress(v));
        }

        internal static UIntPtr ToAddress(EMU i) {
            return Magic.addressOf(i);
        }
    }

    // The StringState enum is only used in String.cs, but kept here because
    // of the dependence between the values used and the format of the MultiUseWord.
    // We require that the values are all contained within PAYLOAD_MASK.

    public enum StringState {
        Undetermined =  0, // Undetermined == 0 assumed in MultiUseWord.cs
        HighChars =     8,
        FastOps =      16,
        SpecialSort =  24,
    }
}
