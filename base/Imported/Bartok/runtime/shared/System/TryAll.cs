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

******************** See below for known problems ********************

This class provides the run-time support for "try_all { ... }" blocks
(i.e. exception handlers with roll-back) and for "atomic { ... }"
blocks implemented over STM.

Overview
--------

Static methods on TryAllManager provide the entry points from compiled
code.  The per-thread TryAllManager objects that are passed in are
instantiated the first time a thread invokes startTryAll.

NB : for most entry points there are variants that take a
TryAllManager and variants that look up the TryAllManager from the
current thread.  The former are used when
StageControlOptions.TryAllOptimisePass is enabled (intended to be the
default).  The latter are there for performance comparisons.

Names in this file reflect the try_all origin of the code.  In
practice a try_all is simply an atomic block that (a) doesn't enlist
the objects that it works on and therefore can't fail with
AtomicIsInvalidException and, (b) doesn't catch
AtomicIsInvalidException and use that to prompt automatic
re-execution.

The external entry points are as follows:

 - startTryAll  - start a new try_all / atomic

 - commit       - attempt to commit the current try_all / atomic

 - abort        - abort the current try_all / atomic

 - validate     - validate the current atomic

 - EnlistNewObjForUpdate - Add the specified newly-allocated object to the 
                  transaction.  If StageControlOptions.AtomicTrackTransactionLocals 
                  is set then we distinguish newly allocated objects from ordinary
                  update enlistments.

 - Enlist[X]for[Y] where X is in {Addr, Indirect, Obj} and Y is in {Read, Update}
                - Add the specified item to the set for read-only access or
                  read-write access in the current atomic block.  "Obj"
                  operations take an object reference.  "Addr" operations take
                  the address of a static field.  "Indirect" operations take
                  an arbitrary address and byte size.

 - Log*         - Log the current contents of the specified data before it
                  may be updated.  Variants specify ref/val (whether the 
                  data being updated is a reference type or a value type)
                  and heap/indirect (whether the data is identified by
                  an object & offset (object == null for statics), or 
                  by a pointer).

 - RegisterForUndo - Register a call-back for execution during an
                  abort.  See Shinnar et al's paper for a discussion
                  of the semantics: currently the heap is rolled back
                  to the point of registration, then the call-back
                  executes, then roll-back continues.  If the
                  call-back raises an exception then it itself is
                  rolled back and the exception silently dropped.

The caller must guarantee that:

 - commit / abort / validate / enlist* / log* are only invoked when there is
   an active try_all or atomic.

 - before a data item is read, an enlist-for-read or enlist-for-update
   has been issued that covers it (since the earliest active
   startTryAll on that manager).

 - before a data item is updated, an enlist-for-update has been issued
   that covers it (since the earliest active startTryAll on that
   manager) and a log call has been made for the item (since the most
   recent active startTryAllOnThatManager).

 - within an atomic block, a AtomicIsInvalidException will
   propagate to the edge of an atomic block and cause abort to be
   called.  

The roll-back code here is, of course, largely derived from the
try_all implementation.

Dynamically nested try_all and atomic blocks are notionally
implemented, but I've not tested them at all thoroughly (indeed, I may
have introduced regressions since the original try_all
implementation).

STM
---

In overview:

 - The transactional memory allows application code to perform updates
   in place, with per-transaction logs of the values overwritten.

 - Conflicts between transactions are detected through versioning
   information.  This is normally held in the multi-use-word (MUW) in an
   object's header, but it can be displaced to the external multi-use
   object if the MUW is already in use (e.g. because the object has had
   its hashcode taken, or because it has a lock associated with it).

 - Write enlistments are visible: each object can be enlisted for
   update by at most one transaction at a time.  This is reflected in
   the versioning header.  If there is a conflict when T1 encounters
   an object already enlisted by T2 then, currently T1 becomes invalid
   and is re-executed.

 - Read enlistments are invisible: each object can be enlisted for
   read by more than one transaction at a time; this is reflected
   solely in the per-transaction logs.  Conflicts are detected only in
   calls to commit and validate.

Transaction logs
----------------

Transaction logs are held in the ordinary heap.  Each transaction has
a ReadEnlistmentLog, an UpdateEnlistmentLog and an UpdateLog.  The
read enlistment log is built up during Enlist*forRead calls and
traversed during validation in calls to commit and validate.  The
update enlistment log is built up during Enlist*forUpdate calls and
traversed after validation in calls to commit.  The update log is
built up during Log* operations and traversed only during roll-back.

Each log comprises a linked list of BlockNode objects each holding an
array of length ENLISTMENT_LOG_CHUNK_SIZE or UPDATE_LOG_CHUNK_SIZE
entries as appropriate.  The TryAllManager refers to the head
(i.e. most recent) end of these lists, so adding an entry is usually a
case of writing it into the next slot in the head chunk. 

Log updates are implemented using the functions in the *LogWriter
structures which are embedded in TryAllManager objects using direct
pointers into the array's elements.  I'm intending to replace these
"Add" methods with inline code generation in the compiler (as the
basic write barrier code already is).  This is particularly useful in
the case of read enlistments.  Consistency between the *LogWriter
structures and the fields in the corresponding *Log object is
maintained by the "SyncFromWriter" and "GetWriter" methods.  These are
used when a log chunk overflows, or before/after a GC so we don't need
to deal with the direct pointers.

Interaction with the GC
-----------------------

We use untraced pointers in four places: (1) the Writer structs
contain interior pointers into the current log chunk, (2) the
enlistment logs contain pointes to the versioning word in the header,
(3) the update logs contain pointers to the objects updated, and to
the overwritten values, in UIntPtr fields, (4) the hash table scheme
for reducing duplicates contains interior pointers to the addresses
that have been logged.

The GC deals with these as follows:

(1) the writers are nulled out before GC (PreGCHook) and filled back
in again post GC (PostGCHook).  The GC itself does not need to be 
aware of their contents during collection.

(2), (3) the contents of the enlistment and update logs are visited 
explicitly (see the Visit methods in this file).

(4) the hash table is discarded before GC (PreGCHook) so there
is no need to keep it up to date.

There is one final subtlety about how this code interacts with the GC.  
We must be careful about write barrier entries caused by updates to
reference-typed fields in the data structures used here: any of these
may overflow a SSB barrier and cause a GC.  The danger is that the
Visit methods may miss objects if we're in the course of changing a
log (e.g. splicing on a new chunk) when a GC occurs.  We deal with
this by following two rules:

(1) when splicing on a log chunk we always write to the reference-typed
currentChunk field *before* writing 0 to the scalar nextEntry field.  A
GC will therefore either see the previous state of the log (if it
triggers before the write to currentChunk), or the next state of
the log.  Note that if these fields were written in the opposite 
order then it might see the previous log chunk but with nextEntry
set back to 0: entries in the chunk would not be visited.

(2) when splicing on a log chunk we mark the interior pointers held
in the Writer objects as 'invalid'.  This means that if a GC 
happens while splicing on the chunk that it will use the slow-path
log info (currentChunk and nextEntry) to determine where to scan
from, rather than the fast path info (from the Writer structs) which
may be out of date.

Versioning
----------

Values of type STMHandle hold pointers to the versioning information
for an object.  Two kinds of versioning information is used:

 - A value of type STMSnapshot.  This is just a snapshot of the 
   object's multi-use word.  It is used for detecting conflicts on
   objects that the transaction has enlisted for read: the
   STM guarantees that the STMSnapshot changes whenever an update
   is committed to the object.

 - A value of type STMWord.  This holds either (a) a version number
   for the object, or (b) a pointer into the transaction log of
   a thread that has the object enlisted for update.  It is either
   held in the MUW (if the MUW is not needed for another purpose),
   or externally in the EMU.

Code here is implemented to use STMSnapshots wherever possible because
of the need for extra tests and indirection to obtain the STMWord.
In particular, the fast-path code when enlisting objects for read
will *only* require the STMSnapshot.

See comments below under "version number management" for how we
avoid wrap-around problems in the version number space.

Known problems
--------------

- If the enable bitmap stage control option is set then we use a 
  slow test in UpdateLogWriter.Write(...) as to whether or not the
  calling thread has opened the supplied object for update.  We
  can assume (or assert) this in an atomic block, and we should 
  assume (or assert) the converse in a try_all (unless nested within
  an outer atomic block).  However, we use a dynamic check to
  avoid splitting the Log* operations into try_all and atomic
  variants.

*/


// Enable bitmap runtime options (enlarges update enlistment log entry
// from 16 bytes to 32 bytes)
#define ENABLE_BITMAP

// Verbose runtime tracing
//#define ENABLE_TRACING

// Verbose tracing during GC
//#define ENABLE_GC_TRACING

// Profile individual call sites (needs /StageControl).
//#define ENABLE_PER_CALL_SITE_PROFILING

// Occasionally pretend atomic blocks are invalid
//#define SHAKE                 

namespace System
{
    using Microsoft.Bartok.Runtime;
    using STMHandle = System.MultiUseWord.STMHandle;
    using STMSnapshot = System.MultiUseWord.STMSnapshot;
    using System.Runtime.CompilerServices;
    using System.Runtime.InteropServices;
    using System.Threading;
    using System.GCs;
    
    [RequiredByBartok("AtomicSupport")]
    public class AtomicException : Exception {}

    //----------------------------------------------------------------------
    //
    // AtomicIsInvalidException is the sole way that invalidity is signalled:
    // we assume that transactions generally execute and commit without conflict
    // and so take a bigger hit on dealing with invalid exceptions in order to
    // avoid testing against boolean results.  
    //
    // Code must be prepared to deal with AtomicIsInvalidException being raised
    // until the point where the status field is set to ChosenCommit.
    //
    // If building a non-blocking implementation we could throw
    // AtomicIsInvalidException in asynchronously.

    public sealed class AtomicIsInvalidException : AtomicException {}

    // This Interface allows programs to define manual actions to be taken to
    // recover during a tryall abort. See also TryAllManager.RegisterForUndo
    
    public interface IUndo {
        // Note that when Undo is called, accessible memory should be in the same
        // state as it was when RegisterForUndo was called.
        void Undo();
    }

    //----------------------------------------------------------------------
    //
    // A value of type STMWord holds either:
    //
    //  a. A version number counting the number of times that the object has
    //     been enlisted for update. 
    //
    //  b. A pointer to the UpdateEnlistmentLog.Entry relating to the
    //     transaction that has the object opened for update.
    //
    // These cases are distinguished based on the bit indicated by IS_OWNED_MASK.

    [NoCCtor]
    internal struct STMWord {

         // IS_OWNED_MASK is the bit we claim to distinguish owned / not owned
         // STM words.  PAYLOAD_MASK is what remains after this bit and those
         // used by the multi-use word.
         internal const uint IS_OWNED_MASK       = 0x00000008;
         internal const uint PAYLOAD_MASK        = 0xfffffff0;

 #if DEBUG
         // Constrain us to an artificially small portion of the version number
         // space in debug builds.  This will force us to trigger GCs to
         // reclaim version numbers and to test out the validate-during-GC code
         // paths.
         internal const uint VERSION_MASK        = 0xffff0000;
         internal const int  VERSION_SHIFT       = 16;
 #else
         // During ordinary builds, use the largest version number space
         // available.
         internal const uint VERSION_MASK        = PAYLOAD_MASK;
         internal const int  VERSION_SHIFT       = 4;
 #endif

         internal UIntPtr value;

         // Constructors 

         internal STMWord (UIntPtr value) {
             this.value = value;
         }

         internal STMWord (UIntPtr payload, bool owned) {
             VTable.Assert((payload & PAYLOAD_MASK) == (uint)payload);
             this.value = payload + (UIntPtr)(owned ? IS_OWNED_MASK : 0);
         }

         // Accessors

         internal UIntPtr GetPayload() {
             return (this.value & (UIntPtr)PAYLOAD_MASK);
         }

         internal UIntPtr GetPayloadWhenOwned() {
             VTable.Assert((this.value & IS_OWNED_MASK) == IS_OWNED_MASK);
             return (this.value - IS_OWNED_MASK);
         }

         internal unsafe TryAllManager GetOwner() {
             VTable.Assert((this.value & IS_OWNED_MASK) != 0);
             UIntPtr ptr = (UIntPtr)(this.value - IS_OWNED_MASK);

             UpdateEnlistmentLog.Entry *entry = 
                 (UpdateEnlistmentLog.Entry *) ptr;
             TryAllManager m = TryAllManager.toTryAllManager(Magic.fromAddress(entry -> m));
             return m;
         }

         internal unsafe STMWord GetOwnersVersion() {
             VTable.Assert((this.value & IS_OWNED_MASK) != 0);
             UIntPtr ptr = (UIntPtr)(this.value - IS_OWNED_MASK);
             UpdateEnlistmentLog.Entry *entry = 
                 (UpdateEnlistmentLog.Entry *) ptr;
             STMWord ver = entry -> v;
             TryAllManager.DebugPrint("STMWord={0:x} ptr={1:x} ver={2:x}\n",
                                      __arglist(this.value,
                                                ptr,
                                                ver.value));
             return ver;
         }

         internal bool IsQuiescent() {
             return !IsOwned();
         }

         internal bool IsOwned() {
             return ((this.value & IS_OWNED_MASK) != 0);
         }

         internal STMWord GetNextVersion() {
             return new STMWord((this.value + (1 << STMWord.VERSION_SHIFT)) &
                                (UIntPtr)STMWord.VERSION_MASK);
         }        

         internal unsafe void Visit(DirectReferenceVisitor referenceVisitor)
        {
#if ENABLE_GC_TRACING
            VTable.DebugPrint("Visit STM word {0:x}\n", __arglist(this.value));
#endif
            if (IsOwned()) {
                UIntPtr ownerAddr = GetPayload();
                UpdateEnlistmentLog.Entry *updateEntry;
                updateEntry = (UpdateEnlistmentLog.Entry *) ownerAddr;

                // Map interior pointer back to start of this array of entries
                UIntPtr offset = *(((UIntPtr*)updateEntry) + 3);
                UIntPtr ownerObj = ownerAddr - offset;

                // Visit the array of entries
                referenceVisitor.Visit(&ownerObj);

                // Recompute the interior pointer
                ownerAddr = ownerObj + offset;
                this.value = (ownerAddr) | (UIntPtr)IS_OWNED_MASK;
            }
            TryAllManager.DebugPrintGC("Visit STM word now {0:x}\n", 
                                       __arglist(this.value));
        }

        // Equality tests

        [Inline]
        internal bool Eq(STMWord other) {
            return (this.value == other.value);
        }

        [Inline]
        internal bool Eq(STMSnapshot other) {
            return ((this.value == other.value) ||
                    (this.value == other.GetSTMWord().value));
        }

        [Inline]
        internal bool Neq(STMWord other) {
            return (this.value != other.value);
        }

        // Formatting
        
        public override String ToString() {
            String r = String.Concat("<",
                                     GetPayload().ToString(),
                                     ",",
                                     IsOwned().ToString(),
                                     ">",
                                     "");
            return r;
        }
    }

    //----------------------------------------------------------------------
    //
    // This is the main class that implements the runtime support for tryall
    // clauses.  Just about all functions called from outside the class are
    // static, and they just call the current thread's local version of the
    // function.

    [NoLoggingForUndo]
    [CCtorIsRunDuringStartup]
    [RequiredByBartok("TryAllSupport")]
    public sealed class TryAllManager {

        [MethodImplAttribute(MethodImplOptions.InternalCall)]
        private static extern long RDTSC();

        //----------------------------------------------------------------------
        //
        // Configuration

        [Intrinsic]
        internal static readonly int UPDATE_LOG_CHUNK_SIZE = 7;
        [Intrinsic]
        internal static readonly int ENLISTMENT_LOG_CHUNK_SIZE = 5;
        [Intrinsic]
        internal static readonly bool TRACK_TRANSACTION_LOCALS = false;
        [Intrinsic]
        internal static readonly bool REMOVE_READ_DUPLICATES_AT_GC = false;
        [Intrinsic]
        internal static readonly bool REMOVE_READ_AFTER_UPDATE_AT_GC = false;
        [Intrinsic]
        internal static readonly bool REMOVE_READ_AFTER_UPDATE_AT_ENLISTMENT = false;
        [Intrinsic]
        internal static readonly bool HASHING = false;
        [Intrinsic]
        internal static readonly bool HASHING_FOR_READS = false;
        [Intrinsic]
        internal static readonly bool BITMAP = false;
        [Intrinsic]
        internal static readonly bool EXTERNAL_BITMAP = false;
        [Intrinsic]
        internal static readonly int HASH_MASK = 2047;
        [Intrinsic]
        internal static readonly bool DISABLE_BEFORE_WRITING_LOG = false;
        [Intrinsic]
        internal static readonly bool DISABLE_AFTER_FILTERING = false;
        [Intrinsic]
        internal static readonly bool DISABLE_BEFORE_FILTERING = false;
        [Intrinsic]
        internal static readonly bool DISABLE_ON_METHOD_ENTRY = false;
        [Intrinsic]
        internal static readonly bool DISABLE_HOUSEKEEPING = false;
        [Intrinsic]
        internal static readonly bool ENABLE_PROFILING = false;
#if DEBUG
        // Debug sizes are deliberately small: they ensure that we test the
        // code responsible for chunk management.
        internal const int UNDO_INITIAL_SIZE = 1;
        internal const int MAX_INITIAL_NESTING_DEPTH = 1;
#else
        internal const int UNDO_INITIAL_SIZE = 4;
        internal const int MAX_INITIAL_NESTING_DEPTH = 4;
#endif

        // In debug builds we write this value into log entries that
        // should never be accessed -- e.g. because there's spare space at the 
        // end of a chunk (to avoid fragmenting decomposed reservations),
        // or because there's spare space at the beginning (because compaction
        // did not fill a whole number of chunks).  
#if DEBUG
        internal const uint DEAD_PTR = 0xDEADBEEF;
#endif

        //----------------------------------------------------------------------
        // 
        // Constructor

        internal TryAllManager() {

            // Sanity check configuration
#if !ENABLE_BITMAP
            if (TryAllManager.BITMAP || TryAllManager.EXTERNAL_BITMAP) {
                VTable.DebugPrint("Runtime cannot support bitmap options");
                VTable.DebugBreak();
            }
#endif

            this.savedTryAlls = new TryAll[MAX_INITIAL_NESTING_DEPTH];
            this.locallyAllocatedSTMWord = this.savedTryAlls[0].locallyAllocatedSTMWord;

            this.atomicIsInvalidException = new AtomicIsInvalidException();
            this.tryAllCounters = TryAllCounters.NewRegisteredCounters();
            this.nextSavedTryAll = 0;

            this.updateLog = new UpdateLog();
            UpdateLog.InitWriter(this);

            this.rEnlistmentLog = new ReadEnlistmentLog();
            ReadEnlistmentLog.InitWriter(this);

            this.uEnlistmentLog = new UpdateEnlistmentLog(this);
            UpdateEnlistmentLog.InitWriter(this);

            this.undoLog = new UndoLog();

            this.AllocLocallyAllocatedSTMWords();
            this.InitLocallyAllocatedSTMWords();
            this.startNestedTryAllHelper(true, 0);

            EnsureCache(this);

            // Initialise static fields holding delegates used by the GC.
            // Multiple initialization is OK; the delegates point to static
            // methods.  This lets us (a) avoid work scanning the logs if 
            // no try_all / atomic blocks have been started (e.g. no need to
            // go through the table of threads), (b) let the tree shaker
            // discard more of the implementation of try_all / atomic if
            // support is not enabled.

            visitStrongRefsDelegate = new VisitMethod(TryAllManager.doVisitStrongRefs);
            visitWeakRefsDelegate = new VisitMethod(TryAllManager.doVisitWeakRefs);
            preGCHookDelegate = new GCHookMethod(TryAllManager.doPreGCHook);
            postGCHookDelegate = new GCHookMethod(TryAllManager.doPostGCHook);
        }

        //----------------------------------------------------------------------

        // Each TryAll struct has a special STM word that EnlistNewObjForUpdate
        // places in newly allocated objects.  This identifies locally allocated
        // objects so that we can avoid Enlist* and Log* calls for them. 
        // These STMWords are held in single-entry arrays of
        // UpdateEnlistmentLog.Entry.  This means that they have the same format
        // in memory as ordinary update enlistment log entries.
        // 
        // AllocLocallyAllocatedSTMWords ensures that each TryAll has an
        // UpdateEnlistmentLog.entry[] allocated for it.  
        //
        // InitLocallyAllocatedSTMWords ensures that each TryAll's
        // locallyAllocatedSTMWord refers to the current address of the
        // single element in the UpdateEnlistmentLog.entry[].  (This is
        // needed after allocation and also after GC in case the array
        // has been relocated).

        private void AllocLocallyAllocatedSTMWords() {
            for (int i = 0; i < this.savedTryAlls.Length; i ++) {
                UpdateEnlistmentLog.Entry[] entries;
                entries = this.savedTryAlls[i].locallyAllocatedEntry;
                if (entries == null) {
                    entries = new UpdateEnlistmentLog.Entry[1];
                    this.savedTryAlls[i].locallyAllocatedEntry = entries;
                    VTable.Assert(this.savedTryAlls[i].locallyAllocatedSTMWord.value == 
                                  UIntPtr.Zero);
                }
            }
        }

        private unsafe void InitLocallyAllocatedSTMWords() {
            for (int i = 0; i < this.savedTryAlls.Length; i ++) {
                STMWord stmWord;
                UIntPtr entryAddr;
                UpdateEnlistmentLog.Entry[] entries;

                entries = this.savedTryAlls[i].locallyAllocatedEntry;
                if (entries != null) {

                    // Set up the entry to look like an ordinary update-
                    // enlistment-log entry for this try all manager.
#if DEBUG
                    entries[0].h.addr = (UIntPtr)TryAllManager.DEAD_PTR;
#endif
                    entries[0].m = Magic.addressOf(this);
                    entries[0].v = new STMWord(UIntPtr.Zero);
                    fixed (UpdateEnlistmentLog.Entry *entry = &entries[0]) {
                        entryAddr = (UIntPtr)entry;
                        UIntPtr start = Magic.addressOf(entries);
                        entries[0].offset = (entryAddr) - start;
                        stmWord = new STMWord(entryAddr, true);
                    }
                    
                    this.savedTryAlls[i].locallyAllocatedSTMWord = stmWord;
                }
            }
        }

        //----------------------------------------------------------------------
        //
        // Start, validate, commit, abort, end
        //
        // These are expected to be called "start, validate*, commit"
        // for transactions that attempt to commit, or "start, validate*,
        // abort" for transactions that decide to abort.  Validation is 
        // performed in commit, so explicit calls are needed only to detect 
        // if a transaction is looping.  "end" is used internally in "commit"
        // and "abort" so is not called explicitly.

        [Inline]
        private void startNestedTryAllHelper(bool isAtomic, int saveAt) {
            if (saveAt == savedTryAlls.Length) {
                int curLength = this.savedTryAlls.Length;
                int newLength = curLength * 2;
                TryAll[] temp = new TryAll[newLength];
                Array.Copy(this.savedTryAlls, 0, temp, 0, curLength);
                this.savedTryAlls = temp;
                AllocLocallyAllocatedSTMWords();
                InitLocallyAllocatedSTMWords();
            }

            this.savedTryAlls[saveAt].stackHeight = this.currentTryAllStackHeight;
            UpdateLog.SyncFromWriter(this);
            this.savedTryAlls[saveAt].updateLogAtStart = this.updateLog.CurrentLocation;

            if (isAtomic) {
                ReadEnlistmentLog.SyncFromWriter(this);
                this.savedTryAlls[saveAt].rEnlistmentLogAtStart = 
                    this.rEnlistmentLog.CurrentLocation;

                UpdateEnlistmentLog.SyncFromWriter(this);
                this.savedTryAlls[saveAt].uEnlistmentLogAtStart = 
                    this.uEnlistmentLog.CurrentLocation;

                this.locallyAllocatedSTMWord = this.savedTryAlls[saveAt].locallyAllocatedSTMWord;
            }
        }
      
        [Inline]
        private void startTryAllHelper(bool isAtomic, StackHeight stackHeight) {
            ClaimToken();
            tryAllCounters.IncrementStartTryAll();

            int saveAt = this.nextSavedTryAll++;

            if (saveAt == 0) {
                // We're entering an outermost try-all, no need to actually save
            } else {
                // We're entering a nested try-all
                startNestedTryAllHelper(isAtomic, saveAt);
            }

            if (isAtomic) {
                ReadEnlistmentLogWriter.EnsureLogMemory(this);
                UpdateEnlistmentLogWriter.EnsureLogMemory(this);
            }

            UpdateLogWriter.EnsureLogMemory(this);

            this.currentTryAllStackHeight = stackHeight;
        }

        private void endTryAll(bool isAtomic)
        {
            DebugPrint("{0}: end (after): {1}%{2}%{3}%{4}%{5}\n", 
                       __arglist(isAtomic ? "atomic" : "try_all",
                                 this.nextSavedTryAll - 1,
                                 this.rEnlistmentLog.Size,
                                 this.uEnlistmentLog.Size,
                                 this.updateLog.Size,
                                 this.undoLog.Size));

            this.nextSavedTryAll--;
            if(this.nextSavedTryAll == 0) {
                // Finished outermost block
                DebugPrint("Clearing logs\n");
                this.updateLog.ResetTo(savedTryAlls[0].updateLogAtStart);
                UpdateLog.InitWriter(this);

            } else {
                // Finished nested block.  
                this.currentTryAllStackHeight = 
                    this.savedTryAlls[nextSavedTryAll].stackHeight;

                if (isAtomic) {
                    this.locallyAllocatedSTMWord = this.savedTryAlls[nextSavedTryAll].locallyAllocatedSTMWord;
                }
                
                // If we finished an atomic block then propagate the
                // invalidity exception upwards.  This is really a
                // policy decision: if we could confirm that the
                // enclosing transaction was valid then we could retry
                // the inner one.

                if (this.currentTryAllStatus == TryAllStatus.Invalid) {
                    if (isAtomic) {
                        DebugPrint("Enclosing transaction still invalid\n");
                        throw this.atomicIsInvalidException;
                    } else {
                        this.currentTryAllStatus = TryAllStatus.Active;
                    }
                }
            }
        }

        internal void becomeInvalid(bool duringGC) {
            DebugPrint("Becoming invalid\n");
            VTable.Assert((this.currentTryAllStatus == TryAllStatus.Active) ||
                          (this.currentTryAllStatus == TryAllStatus.Invalid));
            this.currentTryAllStatus = TryAllStatus.Invalid;
            if (!duringGC) {
                this.tryAllCounters.IncrementInvalidOutsideGC();
                throw this.atomicIsInvalidException;
            } else {
                this.tryAllCounters.IncrementInvalidDuringGC();
            }
        }

        private unsafe void validateHelper() {
            Shake(false); // Not during GC
            TryAllStatus s = this.currentTryAllStatus;
            if (s == TryAllStatus.Invalid) {
                DebugPrint("Transaction previously invalid\n");
                throw this.atomicIsInvalidException;
            } else {
                VTable.Assert(s == TryAllStatus.Active);

                ReadEnlistmentLog.SyncFromWriter(this);
                UpdateEnlistmentLog.SyncFromWriter(this);
                this.rEnlistmentLog.Validate(this,
                                             false); // Not during GC

                DebugPrint("Validation successful\n");
            }
        }

        [Inline]
#if !DEBUG
        [DisableBoundsChecks]
        [DisableNullChecks]
#endif // !DEBUG
        private unsafe void commitHelper(bool isAtomic) {
            VTable.Assert((this.currentTryAllStatus == TryAllStatus.Active) ||
                          (this.currentTryAllStatus == TryAllStatus.Invalid));

            if (isAtomic) {
                ReadEnlistmentLog.SyncFromWriter(this);
                UpdateEnlistmentLog.SyncFromWriter(this);
                Shake(false); // Not during GC

                if (this.currentTryAllStatus == TryAllStatus.Invalid) {
                    becomeInvalid(false); // Not during GC
                }

                this.rEnlistmentLog.Validate(this, 
                                             false); // Not during GC

                if (this.nextSavedTryAll == 1) {
                    DebugPrint("Finished outermost transaction\n");
                    
                    // Finished outermost try_atomic -- dismiss enlistments
                    
                    this.tryAllCounters.IncrementCommitSucceeded();
                    
                    ReadEnlistmentLog.Location rEnlistmentLogAtStart;
                    rEnlistmentLogAtStart = this.savedTryAlls[0].rEnlistmentLogAtStart;
                    this.rEnlistmentLog.DismissFrom(this, rEnlistmentLogAtStart);
                    ReadEnlistmentLog.InitWriter(this);

                    UpdateEnlistmentLog.Location uEnlistmentLogAtStart;
                    uEnlistmentLogAtStart = this.savedTryAlls[0].uEnlistmentLogAtStart;
                    this.uEnlistmentLog.DismissFrom(this, uEnlistmentLogAtStart);
                    UpdateEnlistmentLog.InitWriter(this);

                } else {
                    DebugPrint("Finished nested transaction\n");
                }
            } else {
                this.tryAllCounters.IncrementCommitSucceeded();
            }

            endTryAll(isAtomic);
        }

        private unsafe void AbortHelper(bool isAtomic) {
            bool takeAction;

            if (isAtomic) {
                ReadEnlistmentLog.SyncFromWriter(this);
                UpdateEnlistmentLog.SyncFromWriter(this);
            }

            UpdateLog.SyncFromWriter(this);

            int curTryAll = (this.nextSavedTryAll - 1);
            UpdateLog.Location updateLogAtStart;
            updateLogAtStart = this.savedTryAlls[curTryAll].updateLogAtStart;

            // we must undo back to the state the top action was in,
            // execute the action, and continue.
            do {
                DebugPrint("Depth {0}\n", 
                           __arglist(curTryAll));

                UpdateLog.Location undoUpdatesFrom = updateLogAtStart;
                takeAction = false;
                int lastEntry = this.undoLog.nextEntry - 1;

                if (lastEntry >= 0) {
                    UpdateLog.Location undoWasAt;
                    undoWasAt = this.undoLog.entries[lastEntry].updateLogAtRegistration;

                    if ((curTryAll == 0) || updateLogAtStart.LtEq(undoWasAt)) {
                        // the undo object is part of the current tryall
                        takeAction = true;
                        undoUpdatesFrom = undoWasAt;
                    }
                } 

                DebugPrint(" takeAction: {0} undoUpdatesFrom: {1}\n", 
                           __arglist(takeAction ? "True" : " False",
                                     updateLogAtStart.entry));

                this.updateLog.RollBack(this, 
                                        currentTryAllStackHeight, 
                                        undoUpdatesFrom);

                UpdateLog.InitWriter(this);

                if(takeAction) {
                    // get the undo object.
                    IUndo ua = this.undoLog.entries[lastEntry].UndoAction;
                    // book-keeping. must do before undo call.
                    this.undoLog.entries[lastEntry].UndoAction = null;
                    this.undoLog.nextEntry--;
                    // at this point, nested tryAlls are allowed (which is needed,
                    // since callUndo uses them).  call the registered Undo
                    // function
                    callUndo(ua);
                }
            } while(takeAction);

            if (isAtomic) {
                // Dismiss enlistments made in the aborted section
                
                ReadEnlistmentLog.Location rEnlistmentsStartAt;
                rEnlistmentsStartAt = savedTryAlls[curTryAll].rEnlistmentLogAtStart;
                this.rEnlistmentLog.DismissFrom(this, rEnlistmentsStartAt);
                ReadEnlistmentLog.InitWriter(this);

                UpdateEnlistmentLog.Location uEnlistmentsStartAt;
                uEnlistmentsStartAt = savedTryAlls[curTryAll].uEnlistmentLogAtStart;
                this.uEnlistmentLog.DismissFrom(this, uEnlistmentsStartAt);
                UpdateEnlistmentLog.InitWriter(this);
            }
          
            endTryAll(isAtomic);

            if (isAtomic) {
                this.currentTryAllStatus = TryAllStatus.Active;
            }                
        }

        internal static TryAllManager CurrentTryAll {
            get {
                Thread currentThread = Thread.CurrentThread;
                VTable.Assert(currentThread != null, "no running thread");
                VTable.Assert(currentThread.tryAllManager != null,
                              "no running TryAll");
                TryAllManager m = currentThread.tryAllManager;
                VTable.Deny(m.nextSavedTryAll < 0, "nextSavedTryAll < 0");
                return m;
            }
        }

        internal static TryAllManager CurrentRunningTryAll {
            get {
                TryAllManager m = TryAllManager.CurrentTryAll;
                VTable.Deny(m.nextSavedTryAll == 0,
                            "No running TryAll");
                return m;
            }
        }

        //----------------------------------------------------------------------
        //
        // For now we conflate all static fields to a single object for the
        // purposes of contention detection.

        [RequiredByBartok("AtomicSupport")]
        private static Object objForStaticEnlists = new Object();

#if !DEBUG
        [Inline] [DisableBoundsChecks] [DisableNullChecks]
#endif
        internal static Object AddrToObj(UIntPtr addr) {
            return objForStaticEnlists;
        }
        
        //----------------------------------------------------------------------
        //
        // Object enlistment & update logging

        // EnsureLog operations: ensure that sufficient room is available for subsequent fast stores
#if !DEBUG
        [Inline] [DisableBoundsChecks] [DisableNullChecks]
#endif
        internal static void EnsureLogMemoryHelperForUpdateEnlistmentLog(uint bytesNeeded, TryAllManager m) {
            m.tryAllCounters.IncrementEnsureLogMemoryForUpdateEnlistmentLog(bytesNeeded);
            UpdateEnlistmentLogWriter.EnsureLogMemory(m, bytesNeeded);
        }

#if !DEBUG
        [Inline] [DisableBoundsChecks] [DisableNullChecks]
#endif
        internal static void EnsureLogMemoryHelperForReadEnlistmentLog(uint bytesNeeded, TryAllManager m) {
            m.tryAllCounters.IncrementEnsureLogMemoryForReadEnlistmentLog(bytesNeeded);
            ReadEnlistmentLogWriter.EnsureLogMemory(m, bytesNeeded);
        }

#if !DEBUG
        [Inline] [DisableBoundsChecks] [DisableNullChecks]
#endif
        internal static void EnsureLogMemoryHelperForUpdateLog(uint bytesNeeded, TryAllManager m) {
            m.tryAllCounters.IncrementEnsureLogMemoryForUpdateLog(bytesNeeded);
            UpdateLogWriter.EnsureLogMemory(m, bytesNeeded);
        }
        

#if !DEBUG
        [Inline] [DisableBoundsChecks] [DisableNullChecks]
#endif
        internal static void EnlistObjHelperForRead(Object obj, TryAllManager m) {
            m.tryAllCounters.IncrementEnlistObjForRead();
            STMHandle h = new STMHandle(obj);
            ReadEnlistmentLogWriter.Write(m, h, true); 
        }

#if !DEBUG
        [Inline] [DisableBoundsChecks] [DisableNullChecks]
#endif
        internal static void EnlistObjHelperForReadFast(Object obj, TryAllManager m) {
            m.tryAllCounters.IncrementEnlistObjForReadFast();
            STMHandle h = new STMHandle(obj);
            ReadEnlistmentLogWriter.Write(m, h, false); 
        }

#if !DEBUG
        [Inline] [DisableBoundsChecks] [DisableNullChecks]
#endif
        internal static void EnlistObjHelperForUpdate(Object obj, TryAllManager m) {
            m.tryAllCounters.IncrementEnlistObjForUpdate();
            STMHandle h = new STMHandle(obj);
            UpdateEnlistmentLogWriter.Write(m, h, true);
        }

#if !DEBUG
        [Inline] [DisableBoundsChecks] [DisableNullChecks]
#endif
        internal static void EnlistObjHelperForUpdateFast(Object obj, TryAllManager m) {
            m.tryAllCounters.IncrementEnlistObjForUpdateFast();
            STMHandle h = new STMHandle(obj);
            UpdateEnlistmentLogWriter.Write(m, h, false);
        }

#if !DEBUG
        [Inline] [DisableBoundsChecks] [DisableNullChecks]
#endif
        internal static void EnlistNewObjHelperForUpdate(Object obj, TryAllManager m) {
            m.tryAllCounters.IncrementEnlistNewObjForUpdate();
            STMHandle h = new STMHandle(obj);
            UpdateEnlistmentLogWriter.WriteNew(m, h, true);
        }

#if !DEBUG
        [Inline] [DisableBoundsChecks] [DisableNullChecks]
#endif
        internal static void EnlistNewObjHelperForUpdateFast(Object obj, TryAllManager m) {
            m.tryAllCounters.IncrementEnlistNewObjForUpdateFast();
            STMHandle h = new STMHandle(obj);
            UpdateEnlistmentLogWriter.WriteNew(m, h, false);
        }

#if !DEBUG
        [Inline] [DisableBoundsChecks] [DisableNullChecks]
#endif
        internal static void EnlistAddrHelperForRead(UIntPtr pobj, TryAllManager m) {
            m.tryAllCounters.IncrementEnlistAddrForRead();
            Object obj = AddrToObj(pobj);
            STMHandle h = new STMHandle(obj);
            ReadEnlistmentLogWriter.Write(m, h, true);  
        }

#if !DEBUG
        [Inline] [DisableBoundsChecks] [DisableNullChecks]
#endif
        internal static void EnlistAddrHelperForReadFast(UIntPtr pobj, TryAllManager m) {
            m.tryAllCounters.IncrementEnlistAddrForReadFast();
            Object obj = AddrToObj(pobj);
            STMHandle h = new STMHandle(obj);
            ReadEnlistmentLogWriter.Write(m, h, false);  
        }

#if !DEBUG
        [Inline] [DisableBoundsChecks] [DisableNullChecks]
#endif
        internal static void EnlistAddrHelperForUpdate(UIntPtr pobj, TryAllManager m) {
            m.tryAllCounters.IncrementEnlistAddrForUpdate();
            Object obj = AddrToObj(pobj);
            STMHandle h = new STMHandle(obj);
            UpdateEnlistmentLogWriter.Write(m, h, true);
        }

#if !DEBUG
        [Inline] [DisableBoundsChecks] [DisableNullChecks]
#endif
        internal static void EnlistAddrHelperForUpdateFast(UIntPtr pobj, TryAllManager m) {
            m.tryAllCounters.IncrementEnlistAddrForUpdateFast();
            Object obj = AddrToObj(pobj);
            STMHandle h = new STMHandle(obj);
            UpdateEnlistmentLogWriter.Write(m, h, false);
        }

#if !DEBUG
        [Inline] [DisableBoundsChecks] [DisableNullChecks]
#endif
        internal static bool FilterLog(TryAllManager m,
                                       UIntPtr addr,
                                       UpdateLog.EntryKind kind) {
            if (HASHING) {
                DebugPrint("CheckCache for {0} {1} ", __arglist(addr, (int)kind));
                
                uint[] cache = m.addressCache;
                VTable.Assert(cache != null);
                uint hash = (((uint)addr) >> 2) & (uint) TryAllManager.HASH_MASK;
                
                DebugPrint("Hashes to {0} mask={1} ", 
                           __arglist(hash,
                                     TryAllManager.HASH_MASK));
                
                uint key = ((uint)addr) ^ ((uint)m.tokens);
                if (cache[hash] == (uint) key) {
                    DebugPrint("Found\n");
                    m.tryAllCounters.IncrementUpdateHitInCache(kind);
                    return true;
                } else {
                    DebugPrint("Not found\n");
                    cache[hash] = (uint) key;
                    return false;
                }
            } else {
                return false;
            }
        }

#if !DEBUG
        [Inline] [DisableBoundsChecks] [DisableNullChecks]
#endif
        internal static bool FilterLog(TryAllManager m,
                                       Object obj, 
                                       UIntPtr off,
                                       UpdateLog.EntryKind kind) {
            return FilterLog(m, Magic.addressOf(obj) + off, kind);
        }

#if !DEBUG
        [Inline] [DisableBoundsChecks] [DisableNullChecks]
#endif
        internal static void LogValHeapHelper(Object obj, UIntPtr off,
                                              TryAllManager m) {
            m.tryAllCounters.IncrementLogValHeap();

            if (DISABLE_BEFORE_FILTERING) {
                return;
            }

            if (!FilterLog(m, obj, off, UpdateLog.EntryKind.HEAP_VAL)) {

                if (TryAllManager.DISABLE_AFTER_FILTERING) {
                    return;
                }

                UpdateLogWriter.Write(m,
                                      UpdateLog.EntryKind.HEAP_VAL, 
                                      obj, 
                                      off,
                                      true, true,
                                      true);
            }
        }

#if !DEBUG
        [Inline] [DisableBoundsChecks] [DisableNullChecks]
#endif
        internal static void LogValHeapHelperFast(Object obj, UIntPtr off,
                                              TryAllManager m) {
            m.tryAllCounters.IncrementLogValHeapFast();

            if (DISABLE_BEFORE_FILTERING) {
                return;
            }

            if (!FilterLog(m, obj, off, UpdateLog.EntryKind.HEAP_VAL)) {

                if (TryAllManager.DISABLE_AFTER_FILTERING) {
                    return;
                }

                UpdateLogWriter.Write(m,
                                      UpdateLog.EntryKind.HEAP_VAL, 
                                      obj, 
                                      off,
                                      true, true,
                                      false);
            }
        }

#if !DEBUG
        [Inline] [DisableBoundsChecks] [DisableNullChecks]
#endif
        private static void LogRefHeapHelper(Object obj, UIntPtr off,
                                             TryAllManager m) {
            m.tryAllCounters.IncrementLogRefHeap();

            if (DISABLE_BEFORE_FILTERING) {
                return;
            }

            if (!FilterLog(m, obj, off, UpdateLog.EntryKind.HEAP_REF)) {

                if (TryAllManager.DISABLE_AFTER_FILTERING) {
                    return;
                }

                UpdateLogWriter.Write(m,
                                      UpdateLog.EntryKind.HEAP_REF, 
                                      obj, 
                                      off,
                                      true, true,
                                      true);
            }
        }

#if !DEBUG
        [Inline] [DisableBoundsChecks] [DisableNullChecks]
#endif
        private static void LogRefHeapHelperFast(Object obj, UIntPtr off,
                                             TryAllManager m) {
            m.tryAllCounters.IncrementLogRefHeapFast();

            if (DISABLE_BEFORE_FILTERING) {
                return;
            }

            if (!FilterLog(m, obj, off, UpdateLog.EntryKind.HEAP_REF)) {

                if (TryAllManager.DISABLE_AFTER_FILTERING) {
                    return;
                }

                UpdateLogWriter.Write(m,
                                      UpdateLog.EntryKind.HEAP_REF, 
                                      obj, 
                                      off,
                                      true, true,
                                      false);
            }
        }

#if !DEBUG
        [Inline] [DisableBoundsChecks] [DisableNullChecks]
#endif
        internal static void LogValStaticHelper(UIntPtr addr,
                                                TryAllManager m) {
            m.tryAllCounters.IncrementLogValHeap();

            if (DISABLE_BEFORE_FILTERING) {
                return;
            }

            if (!FilterLog(m, addr, UpdateLog.EntryKind.HEAP_VAL)) {

                if (TryAllManager.DISABLE_AFTER_FILTERING) {
                    return;
                }

                UpdateLogWriter.Write(m,
                                      UpdateLog.EntryKind.HEAP_VAL, 
                                      null,
                                      addr,
                                      false,
                                      false,
                                      true);
            }
        }

#if !DEBUG
        [Inline] [DisableBoundsChecks] [DisableNullChecks]
#endif
        internal static void LogValStaticHelperFast(UIntPtr addr,
                                                    TryAllManager m) {
            m.tryAllCounters.IncrementLogValHeapFast();

            if (DISABLE_BEFORE_FILTERING) {
                return;
            }

            if (!FilterLog(m, addr, UpdateLog.EntryKind.HEAP_VAL)) {

                if (TryAllManager.DISABLE_AFTER_FILTERING) {
                    return;
                }

                UpdateLogWriter.Write(m,
                                      UpdateLog.EntryKind.HEAP_VAL, 
                                      null,
                                      addr,
                                      false,
                                      false,
                                      false);
            }
        }

#if !DEBUG
        [Inline] [DisableBoundsChecks] [DisableNullChecks]
#endif
        private static void LogRefStaticHelper(UIntPtr addr,
                                               TryAllManager m) {
            m.tryAllCounters.IncrementLogRefHeap();

            if (DISABLE_BEFORE_FILTERING) {
                return;
            }

            if (!FilterLog(m, addr, UpdateLog.EntryKind.HEAP_REF)) {

                if (TryAllManager.DISABLE_AFTER_FILTERING) {
                    return;
                }

                UpdateLogWriter.Write(m,
                                      UpdateLog.EntryKind.HEAP_REF, 
                                      null,
                                      addr,
                                      false,
                                      false,
                                      true);
            }
        }

#if !DEBUG
        [Inline] [DisableBoundsChecks] [DisableNullChecks]
#endif
        private static void LogRefStaticHelperFast(UIntPtr addr,
                                                   TryAllManager m) {
            m.tryAllCounters.IncrementLogRefHeapFast();

            if (DISABLE_BEFORE_FILTERING) {
                return;
            }

            if (!FilterLog(m, addr, UpdateLog.EntryKind.HEAP_REF)) {

                if (TryAllManager.DISABLE_AFTER_FILTERING) {
                    return;
                }

                UpdateLogWriter.Write(m,
                                      UpdateLog.EntryKind.HEAP_REF, 
                                      null,
                                      addr,
                                      false,
                                      false,
                                      false);
            }
        }

#if !DEBUG
        [Inline] [DisableBoundsChecks] [DisableNullChecks]
#endif
        private static void LogIndirectValHeapHelper(UIntPtr pobj,
                                                     TryAllManager m) {

            m.tryAllCounters.IncrementLogIndirectValHeap();

            if (DISABLE_BEFORE_FILTERING) {
                return;
            }

            if (!FilterLog(m, pobj, UpdateLog.EntryKind.HEAP_VAL)) {

                if (TryAllManager.DISABLE_AFTER_FILTERING) {
                    return;
                }

                FactoredPointer factoredPointer = fixupInterior(pobj);
                //                EnsureLogMemory(m, 4);
                UpdateLogWriter.Write(m,
                                      UpdateLog.EntryKind.HEAP_VAL, 
                                      factoredPointer.baseObj,
                                      factoredPointer.offset,
                                      true, 
                                      false,
                                      true);
            }
        }

#if !DEBUG
        [Inline] [DisableBoundsChecks] [DisableNullChecks]
#endif
        private static void LogIndirectValHeapHelperFast(UIntPtr pobj,
                                                     TryAllManager m) {

            m.tryAllCounters.IncrementLogIndirectValHeapFast();

            if (DISABLE_BEFORE_FILTERING) {
                return;
            }

            if (!FilterLog(m, pobj, UpdateLog.EntryKind.HEAP_VAL)) {

                if (TryAllManager.DISABLE_AFTER_FILTERING) {
                    return;
                }

                FactoredPointer factoredPointer = fixupInterior(pobj);
                UpdateLogWriter.Write(m,
                                      UpdateLog.EntryKind.HEAP_VAL, 
                                      factoredPointer.baseObj,
                                      factoredPointer.offset,
                                      true,
                                      false,
                                      false);
            }
        }

#if !DEBUG
        [Inline] [DisableBoundsChecks] [DisableNullChecks]
#endif
        private static void LogIndirectValStackHelper(UIntPtr pobj,
                                                      TryAllManager m) {
            m.tryAllCounters.IncrementLogIndirectValStack();

            if (DISABLE_BEFORE_FILTERING) {
                return;
            }

            if (!FilterLog(m, pobj, UpdateLog.EntryKind.NON_HEAP_VAL)) {

                if (TryAllManager.DISABLE_AFTER_FILTERING) {
                    return;
                }

                UpdateLogWriter.Write(m,
                                      UpdateLog.EntryKind.NON_HEAP_VAL, 
                                      null,
                                      pobj,
                                      false,
                                      false,
                                      true);
            }
        }

#if !DEBUG
        [Inline] [DisableBoundsChecks] [DisableNullChecks]
#endif
        private static void LogIndirectValStackHelperFast(UIntPtr pobj,
                                                      TryAllManager m) {
            m.tryAllCounters.IncrementLogIndirectValStackFast();

            if (DISABLE_BEFORE_FILTERING) {
                return;
            }

            if (!FilterLog(m, pobj, UpdateLog.EntryKind.NON_HEAP_VAL)) {

                if (TryAllManager.DISABLE_AFTER_FILTERING) {
                    return;
                }

                UpdateLogWriter.Write(m,
                                      UpdateLog.EntryKind.NON_HEAP_VAL, 
                                      null,
                                      pobj,
                                      false,
                                      false,
                                      false);
            }
        }

#if !DEBUG
        [Inline] [DisableBoundsChecks] [DisableNullChecks]
#endif
        private static void LogIndirectRefHeapHelper(UIntPtr pobj,
                                                     TryAllManager m) {

            m.tryAllCounters.IncrementLogIndirectRefHeap();

            if (DISABLE_BEFORE_FILTERING) {
                return;
            }

            if (!FilterLog(m, pobj, UpdateLog.EntryKind.HEAP_REF)) {

                if (TryAllManager.DISABLE_AFTER_FILTERING) {
                    return;
                }

                FactoredPointer factoredPointer = fixupInterior(pobj);
                //                EnsureLogMemory(m, 4);
                UpdateLogWriter.Write(m,
                                      UpdateLog.EntryKind.HEAP_REF,
                                      factoredPointer.baseObj, 
                                      factoredPointer.offset,
                                      true,
                                      false,
                                      true);
            }
        }

#if !DEBUG
        [Inline] [DisableBoundsChecks] [DisableNullChecks]
#endif
        private static void LogIndirectRefHeapHelperFast(UIntPtr pobj,
                                                     TryAllManager m) {

            m.tryAllCounters.IncrementLogIndirectRefHeapFast();

            if (DISABLE_BEFORE_FILTERING) {
                return;
            }

            if (!FilterLog(m, pobj, UpdateLog.EntryKind.HEAP_REF)) {

                if (TryAllManager.DISABLE_AFTER_FILTERING) {
                    return;
                }

                FactoredPointer factoredPointer = fixupInterior(pobj);
                UpdateLogWriter.Write(m,
                                      UpdateLog.EntryKind.HEAP_REF,
                                      factoredPointer.baseObj, 
                                      factoredPointer.offset,
                                      true,
                                      false,
                                      false);
            }
        }

#if !DEBUG
        [Inline] [DisableBoundsChecks] [DisableNullChecks]
#endif
        private static void LogIndirectRefStackHelper(UIntPtr pobj,
                                                      TryAllManager m) {
            m.tryAllCounters.IncrementLogIndirectRefStack();

            if (DISABLE_BEFORE_FILTERING) {
                return;
            }

            if (!FilterLog(m, pobj, UpdateLog.EntryKind.NON_HEAP_REF)) {

                if (TryAllManager.DISABLE_AFTER_FILTERING) {
                    return;
                }

                UpdateLogWriter.Write(m,
                                      UpdateLog.EntryKind.NON_HEAP_REF,
                                      null,
                                      pobj,
                                      false,
                                      false,
                                      true);
            }
        }

#if !DEBUG
        [Inline] [DisableBoundsChecks] [DisableNullChecks]
#endif
        private static void LogIndirectRefStackHelperFast(UIntPtr pobj,
                                                      TryAllManager m) {
            m.tryAllCounters.IncrementLogIndirectRefStackFast();

            if (DISABLE_BEFORE_FILTERING) {
                return;
            }

            if (!FilterLog(m, pobj, UpdateLog.EntryKind.NON_HEAP_REF)) {

                if (TryAllManager.DISABLE_AFTER_FILTERING) {
                    return;
                }

                UpdateLogWriter.Write(m,
                                      UpdateLog.EntryKind.NON_HEAP_REF,
                                      null,
                                      pobj,
                                      false,
                                      false,
                                      false);
            }
        }

        //----------------------------------------------------------------------
        //
        // Version number management
        //
        // We increment an object's version number each time we commit
        // or abort a transaction that has enlisted it for update.  We
        // let version numbers wrap around when the number of bits
        // available to store them in the STM word overflows.
        //
        // In order to make this safe we must make sure that a
        // transaction which has a read enlistment for an earlier use
        // of a version number is no longer running when we might
        // re-use that version number in the same object.
        //
        // We do that by ensuring that we validate all of the running
        // transactions at least once every N transactions where N is
        // no larger than the number of version numbers that are
        // available.  
        //
        // After validation, each object is either (a) not enlisted by
        // any transaction, (b) enlisted for update by one transaction
        // and possibly enlisted for read by that same transaction, or
        // (c) enlisted for read by a number of valid transactions.  This
        // lets us make a further complete cycle through the version number
        // space.
        //
        // In practice we always validate at GC and so we need only make sure
        // that GCs occur sufficiently often.
        //
        // We detect when we need to force validation by allocating
        // "transaction tokens" to TryAllManagers.  A TryAllManager
        // must have a transaction token in order to start a new
        // transaction.  We give out batches of transaction tokens to
        // TryAllManagers so that they can start transactions without
        // contending for a single shared count.  We force validation
        // when have given out all the batches that are available.
        //
        // Tokens are replenished at every GC: as long as GCs happen
        // sufficiently often we'll never need to force one.  NB: in a 
        // release build with 3 bits taken out of the version number 
        // we're left with N = 2^29, about 500 million transactions.

        const uint TOKEN_BATCH_SIZE = 128;
        const uint MAX_TOKENS = (STMWord.VERSION_MASK >> STMWord.VERSION_SHIFT);
        const int MAX_BATCHES = (int)(MAX_TOKENS / TOKEN_BATCH_SIZE);
        
        static int batchesAvailable = MAX_BATCHES;

        [NoInline]
        internal void ClaimTokens() {

            DebugPrint("{0:x}: Claiming tokens\n",
                              __arglist(Magic.addressOf(this)));

            // Try to claim one of the batches currently available.
            int available;
            do {
                available = batchesAvailable;

                // If there are no batches available (or periodically if
                // SHAKE debugging is enabled) force a GC to replenish
                // the supply.
                if ((available == 0) || (Occasionally())) {
                    tryAllCounters.IncrementForcedGC();
                    GC.Collect();
                    available = batchesAvailable;
                }
            } while (Interlocked.CompareExchange(ref batchesAvailable,
                                                 (available - 1),
                                                 available) != available);

            DebugPrint("{0:x}: Got tokens, now {1} batches available\n",
                       __arglist(Magic.addressOf(this), batchesAvailable));

            tokens = TOKEN_BATCH_SIZE;

            VTable.Assert(TOKEN_BATCH_SIZE < TryAllManager.HASH_MASK);

            TryAllManager.ClearCache(this);
        }

        internal void ClaimToken() {
            // Get a new batch of tokens if our current batch is
            // exhausted.
            if (this.tokens == 0) {
                ClaimTokens();
            }

            // Get a token from our current batch
            this.tokens --;
            DebugPrint("{0} tokens remain\n", __arglist(this.tokens));
        }

        internal static void ReplenishTokens() {
            if (TryAllManager.ENABLE_PROFILING) {
                if (VTable.enableGCTiming) {
                    VTable.DebugPrint("[Token batches before: {0} after: {1}]\n",
                                      __arglist(batchesAvailable, MAX_BATCHES));
                }
            }

            // Make sure that we generate > 0 batches -- this may fail if the
            // settings of VERSION_MASK and VERSION_SHIFT leave fewer than
            // TOKEN_BATCH_SIZE tokens available.  

            VTable.Assert(MAX_BATCHES > 0, "Too few tokens to make a single batch");
            
            batchesAvailable = MAX_BATCHES;
        }

        //----------------------------------------------------------------------
        //
        // GC support
        //
        // We interact with the GC in two ways.  (1) During GC we make sure that the
        // log state is held in the nextEntry fields rather than cached in the
        // writer structures; this means we don't have to worry about fixing up
        // the pointers.  (2) We need to manually traverse the logs to visit 
        // pointers to objects which are held (a) in UIntPtr typed fields in the
        // update log and (b) implicitly in STMHandle structures in the enlistment
        // logs.
        //
        // NB: all pointers reads during the GC must be made through
        // the ReadBarrier function below -- otherwise we can't be sure if the
        // field may have already been visited.  

        internal static
        void VisitStrongRefs(DirectReferenceVisitor referenceVisitor)
        {
            if (visitStrongRefsDelegate != null) {
                visitStrongRefsDelegate(referenceVisitor);
            }
        }

        internal static 
        void VisitWeakRefs(DirectReferenceVisitor referenceVisitor) 
        {
            if (visitWeakRefsDelegate != null) {
                visitWeakRefsDelegate(referenceVisitor);
            }
        }

        internal static void PreGCHookTryAll() 
        {
            if (preGCHookDelegate != null) {
                preGCHookDelegate();
            }
        }

        internal static void PostGCHookTryAll() 
        {
            if (postGCHookDelegate != null) {
                postGCHookDelegate();
            }
        }

        // Called after stopping the world and before tracing begins.  This is 
        // responsible for:
        //
        //    a. clearing the pointer-derived values held in UIntPtrs that won't
        //       be explicitly visited during GC.
        //
        //    b. Validating all of the running transactions.  We do that *before*
        //       GC so that (i) we can recover space used by the enlistment logs of 
        //       invalid transactions, (ii) we can recover space used by duplicate
        //       log entries, (iii) we can assume that transactions are valid
        //       when visiting their logs.

        internal static void doPreGCHook() {
            SetDuringGC(true);
            TryAllManager.DebugPrintNoLock("PreGC callback\n");
            Thread[] threadTable = Thread.threadTable;
            int limit = threadTable.Length;
            
            for (int i = 0; i < limit; i++) {
                Thread thread = threadTable[i];
                if (thread != null) {
                    TryAllManager m = thread.tryAllManager;
                    if(m != null) {
                        RemoveCache(m);
                        UpdateLog.SyncFromWriter(m);
                        ReadEnlistmentLog.SyncFromWriter(m);
                        UpdateEnlistmentLog.SyncFromWriter(m);

                        if (TryAllManager.REMOVE_READ_AFTER_UPDATE_AT_GC ||
                            TryAllManager.REMOVE_READ_DUPLICATES_AT_GC) {
                            m.rEnlistmentLog.ValidateAndRemoveDuplicates(m);
                        } else {
                            m.rEnlistmentLog.Validate(m, true /* during GC */);
                        }
                    }
                }
            }
        }

        // Called before resuming the world.  This is responsible for
        // validation, removing duplicates from the logs and restoring
        // untraced pointers in the fast-path writer structs.  In
        // theory we could perform the operations on the logs when
        // visiting them -- but this is tricky code and separating it
        // out lets us work without needing GC barriers.

        internal static void doPostGCHook() {
            Thread[] threadTable = Thread.threadTable;
            int limit = threadTable.Length;

            TryAllManager.DebugPrintNoLock("PostGC callback\n");

            // 1. Restore STMWords for locally allocated objects and
            //    hashtables for duplicate detection

            for (int i = 0; i < limit; i++) {
                Thread thread = threadTable[i];
                if (thread != null) {
                    TryAllManager m = thread.tryAllManager;
                    if(m != null) {
                        EnsureCache(m); 
                        // NB: we do not call AllocLocallyAllocatedSTMWords here:
                        // we haven't completely finished the current GC and don't
                        // wish to risk triggering further GCs by allocating
                        // new UpdateEnlistmentLog.Entry arrays for any TryAll
                        // structs that don't have one yet.  (This could happen
                        // if the current GC was triggered by such an allocation)
                        m.InitLocallyAllocatedSTMWords();

                        if (m.nextSavedTryAll == 0) { 
                            m.locallyAllocatedSTMWord = m.savedTryAlls[0].locallyAllocatedSTMWord;
                        } else {
                            m.locallyAllocatedSTMWord = m.savedTryAlls[m.nextSavedTryAll - 1].locallyAllocatedSTMWord;
                        }
                    }
                }
            }

            // 2. Replenish supply of transaction tokens
            TryAllManager.ReplenishTokens();

            // 3. Restore fast-path writer structs and STMWords for locally
            //    allocated objects
            for (int i = 0; i < limit; i++) {
                Thread thread = threadTable[i];
                if (thread != null) {
                    TryAllManager m = thread.tryAllManager;
                    if(m != null) {
                        if (UpdateLog.WriterIsValid(m._updateLogWriter)) {
                            UpdateLog.InitWriter(m);
                        }
                        if (ReadEnlistmentLog.WriterIsValid(m._rEnlistmentLogWriter)) {
                            ReadEnlistmentLog.InitWriter(m);
                        }
                        if (UpdateEnlistmentLog.WriterIsValid(m._uEnlistmentLogWriter)) {
                            UpdateEnlistmentLog.InitWriter(m);
                        }
                    }
                }
            }

            SetDuringGC(false);
        }

        // We ensure that all of our own data structures held in objects and read
        // during GC must have been visited.  For the semispace collector this 
        // ensures that they are in to-space with a valid vtable pointer.
        // This makes the code less brittle to the ordering of special cases 
        // during GC -- e.g. we can be run after dealing with pinned objects 
        // (some of which may lie on the same page as our data structures).

        internal unsafe static Object ReadBarrier(DirectReferenceVisitor v,
                                                  Object o)
        {
            Object result;
            if (o == null) {
                result = null;
            } else {
                UIntPtr temp = Magic.addressOf(o);
#if ENABLE_GC_TRACING
                VTable.DebugPrint("rb({0:x}) -> ", 
                                  __arglist((uint)Magic.addressOf(o)));
#endif

                v.Visit(&temp);
                result = Magic.fromAddress(temp);
#if ENABLE_GC_TRACING
                VTable.DebugPrint("{0:x}\n", 
                                  __arglist((uint)Magic.addressOf(result)));
#endif
            }
            return result;    
        }


        // Intrinsics used to avoid casts from the result returned by
        // ReadBarrier: the collector may use bits in the VTable word and so
        // we cannot use a checked cast.

        [Intrinsic]
        internal static unsafe extern Thread[] 
        toThreadArray(Object o);

        [Intrinsic]
        internal static unsafe extern Thread 
        toThread(Object o);

        [Intrinsic]
        internal static unsafe extern TryAllManager 
        toTryAllManager(Object o);

        [Intrinsic]
        internal static unsafe extern ReadEnlistmentLog 
        toReadEnlistmentLog(Object o);

        [Intrinsic]
        internal static unsafe extern ReadEnlistmentLog.LogChunk
        toReadEnlistmentLogChunk(Object o);

        [Intrinsic]
        internal static unsafe extern ReadEnlistmentLog.Entry[]
        toReadEnlistmentLogEntryArray(Object o);

        [Intrinsic]
        internal static unsafe extern UpdateEnlistmentLog
        toUpdateEnlistmentLog(Object o);

        [Intrinsic]
        internal static unsafe extern UpdateEnlistmentLog.LogChunk
        toUpdateEnlistmentLogChunk(Object o);

        [Intrinsic]
        internal static unsafe extern UpdateEnlistmentLog.Entry[]
        toUpdateEnlistmentLogEntryArray(Object o);

        [Intrinsic]
        internal static unsafe extern UpdateLog
        toUpdateLog(Object o);

        [Intrinsic]
        internal static unsafe extern UpdateLog.LogChunk
        toUpdateLogChunk(Object o);

        [Intrinsic]
        internal static unsafe extern UpdateLog.Entry[]
        toUpdateLogEntryArray(Object o);

        // Visit strong refs from the transaction logs.  These occur only in the 
        // 'old value' entries in the undo log. 
        private static void doVisitStrongRefs(DirectReferenceVisitor rv) {
            TryAllManager.DebugPrintGC("GC - VisitLogData with ptrVisitor={0}\n", 
                                __arglist((uint)Magic.addressOf(rv)));
            
            Thread[] threadTable = toThreadArray(ReadBarrier(rv, 
                                                             Thread.threadTable));
            
            int limit = threadTable.Length;
            for (int i = 0; i < limit; i++) {
                Thread thread = toThread(ReadBarrier(rv, threadTable[i]));
                if (thread != null) {
                    TryAllManager m = toTryAllManager(ReadBarrier(rv,
                                                                  thread.tryAllManager));
                    if(m != null) {
                        TryAllManager.DebugPrintGC("GC - Visiting thread index={0} \n",
                                            __arglist(i));
                        VisitStrongRefs(m, rv);
                    }
                }
            }
        }

        // Visit weak refs from the transaction logs.  These occur in the 
        // reference-directed values identifying objects in all three logs.
        // The log entries can be removed if the referent has died.
        //
        // We split weak ref processing into two phases.  The first phase visits
        // the update-enlistment log.  The second phase visits the 
        // read-enlistment and undo logs.  This simplifies processing of the 
        // read-enlistment log when handling entries that occur in both 
        // enlistment logs.
        private static void doVisitWeakRefs(DirectReferenceVisitor rv) {
            TryAllManager.DebugPrintGC("GC - Visit logs (weak) with {0}\n", 
                                __arglist((uint)Magic.addressOf(rv)));
            
            Thread[] threadTable = toThreadArray(ReadBarrier(rv, 
                                                             Thread.threadTable));
            
            int limit = threadTable.Length;
            
            for (int i = 0; i < limit; i++) {
                Thread thread = toThread(ReadBarrier(rv,
                                                     threadTable[i]));
                if (thread != null) {
                    TryAllManager m =
                        toTryAllManager(ReadBarrier(rv,
                                                    thread.tryAllManager));
                    if(m != null) {
#if ENABLE_GC_TRACING
                        VTable.DebugPrint("GC - Visiting thread index={0} \n",
                                          __arglist(i));
#endif
                        VisitWeakRefsPhase1(m, rv);
                    }
                }
            }
                
            for (int i = 0; i < limit; i++) {
                Thread thread = threadTable[i];
                if (thread != null) {
                    TryAllManager m = thread.tryAllManager;
                    if(m != null) {
                        TryAllManager.DebugPrintGC("GC - Visiting thread index={0} \n",
                                            __arglist(i));
                        VisitWeakRefsPhase2(m, rv);
                    }
                }
            }
        }

        // Visit strong refs from the transaction logs.  These occur in the 
        // overwritten values in the undo log.
        private static void VisitStrongRefs(TryAllManager m,
                                            DirectReferenceVisitor rv) {

            UpdateLog updateLog = toUpdateLog(ReadBarrier(rv, 
                                                          m.updateLog));
            updateLog.VisitStrongRefs(m, rv);
        }

        private static void VisitWeakRefsPhase1(TryAllManager m,
                                                DirectReferenceVisitor rv) {
            UpdateEnlistmentLog uEnlistmentLog = m.uEnlistmentLog;
            uEnlistmentLog.VisitWeakRefs(m, rv);
        }

        private static void VisitWeakRefsPhase2(TryAllManager m,
                                                DirectReferenceVisitor rv) {
            UpdateLog updateLog;
            ReadEnlistmentLog rEnlistmentLog;

            updateLog =
                toUpdateLog(ReadBarrier(rv, m.updateLog));
            rEnlistmentLog =
                toReadEnlistmentLog(ReadBarrier(rv, 
                                                m.rEnlistmentLog));

            updateLog.VisitWeakRefs(m, rv);
            rEnlistmentLog.VisitWeakRefs(m, rv);
        }

        //----------------------------------------------------------------------
        //
        // Hashing
        //
        // If HASHING is set then we keep a fixed sized table 
        // (VTable.tryAllCheckMask entries) which maps from hash values to 
        // addresses that have been logged.  We use this to filter logging requests
        // in order to remove duplicates.  For simplicity we hold only a single
        // address for each hash value.

        private static void ClearCache(TryAllManager m) {
            if (HASHING) {
                DebugPrint("Clearing cache\n");
                uint[] cache = m.addressCache;
                if (cache != null) {
                    System.Array.Clear(cache, 0, cache.Length);
                }
            }
        }

        // Ensure that a cache structure is available.  We do this on the 
        // way out of Log* operation so that we can GC if no cache is available.
        [NoInline]
        internal static void EnsureCache(TryAllManager m) {
            if (HASHING) {
                VTable.Assert(m.addressCache == null);
                DebugPrint("No cache available: creating one\n");
                uint[] cache = new uint[TryAllManager.HASH_MASK + 1];
                m.tryAllCounters.IncrementCachesCreated();
                m.addressCache = cache;
            }
        }

        // Null-out the cache field before GC
        [NoInline]
        internal static void RemoveCache(TryAllManager m) {
            if (HASHING) {
                m.addressCache = null;
            }
        }

        //----------------------------------------------------------------------
        //
        // Undo helpers
        //
        // The implementation here is not thoroughly tested: it's really
        // a placeholder while we think about the programming model.  Some 
        // points to note about this:
        //
        // (a) We associate registered IUndo actions with positions in the 
        //     update log.  When rolling back the log we use these positions
        //     to indicate when to execute each IUndo action.  This causes
        //     a problem with nested try_all blocks which do not contain
        //     logging:  try_all { register-for-undo { try_all { .. } } }.
        //     Without logging we can't tell whether the registered action
        //     is associated with the inner try_all or the outer one.  We
        //     currently deal with this by logging a dummy entry in the log
        //     when registering an undo action.  We could alternatively
        //     record the current try_all nesting depth in the IUndo log.
        //     
        // (b) The current model requires IUndo actions to run with the
        //     state rewound to the point at which they were registered.
        //     This means that registration imposes a barrier across which
        //     Log* operations cannot be optimized.  Two consequences: 
        //     (i) the current compiler does not respect this barrier,
        //     (ii) if implemented correctly it means we cannot bound the
        //     log sizes by the volume of data overwritten.

        private void RegisterForUndoHelper(IUndo ua) {
            // note to compiler: if this function may be invoked at a given point,
            // any point after that must (at least once) backup the value of any
            // data modified after that.  This is like a backup-barrier.  also,
            // code can't migrate through calls to it.

            if(nextSavedTryAll <= 0) {
                return;
            }

            DebugPrint("<TryAll> undo action being registered\n");

            if(ua == null) {
                return;
            }

            this.undoLog.EnsureCapacity();

            // prevent issues with logging right after a StartTryAll().  this code
            // should be done better, and hopefully made optional (with support
            // from the compiler).
            unsafe {
                fixed(UIntPtr* dummyAddress = &TryAllManager.staticDummyLogged) {
                    LogIndirectValStackHelper((UIntPtr)dummyAddress, this);
                }
            }

            // copy indices.
            int ne = (this.undoLog.nextEntry++);

            this.undoLog.entries[ne].updateLogAtRegistration = 
                updateLog.CurrentLocation;

            this.undoLog.entries[ne].UndoAction = 
                ua;
        }

        // this function may not throw an exception
        private void callUndo(IUndo ua) {
            // should probably have 1 static exception for here.

            DebugPrint("<TryAll> Undo action being invoked\n");

            Exception ex = new Exception();
            try {
                try { // tryall
                    DebugPrint(" nesting depth: {0}\n", 
                               __arglist(nextSavedTryAll));
                    ua.Undo();
                    throw ex;
                } catch(System.TryAllFakeException) { }
            } catch (Exception) {
                // catch the exception generated, and do nothing about it.  Note
                // that this means that any exceptions propagated up to this level
                // are squashed.
            }

            DebugPrint("<TryAll> undo finished\n nesting depth: {0}\n",
                       __arglist(nextSavedTryAll));

        }

        //----------------------------------------------------------------------
        //
        // Wrappers called from outside.  These generally default in 
        // the TryAllManager parameter, or expand multi-word operations 
        // into series of invocations on single-word ones.

        public static void RegisterForUndo(IUndo ua) {
            TryAllManager.CurrentRunningTryAll.RegisterForUndoHelper(ua);
        }

        [RequiredByBartok("TryAllSupport")]
        [NoLoggingForUndoAttribute]
#if !DEBUG
        [DisableNullChecks]
        [DisableBoundsChecks]
#endif // !DEBUG
        internal static void StartTryAll(StackHeight stackHeight) {
            VTable.Assert(!TryAllManager.DISABLE_HOUSEKEEPING);
            DebugPrint("start try_all (slow)\n");
            
            Thread currentThread = Thread.CurrentThread;
            if(currentThread.tryAllManager == null) {
                currentThread.tryAllManager = new TryAllManager();
            }
            currentThread.tryAllManager.startTryAllHelper(false /*try_all*/,
                                                          stackHeight);
        }

        [RequiredByBartok("TryAllSupport")]
        [NoLoggingForUndoAttribute]
#if !DEBUG
        [DisableNullChecks]
        [DisableBoundsChecks]
#endif // !DEBUG
        internal static void StartTryAll(StackHeight stackHeight, 
                                         TryAllManager m) {
            VTable.Assert(!TryAllManager.DISABLE_HOUSEKEEPING);
            DebugPrint("start try_all (quick)\n");

            // We may receive a null TryAllManager if this is the first
            // call to StartTryAll made by this thread.  NB, Start/Commit/Abort
            // "may mutate existing storage" in Operator.cs, so subsequent
            // calls will re-read the TryAllManager after we've stored it
            // in the Thread structure.  
            if (m == null) {
                StartTryAll(stackHeight);
            } else {
                m.startTryAllHelper(false /*try_all*/, stackHeight);
            }
        }

        [RequiredByBartok("AtomicSupport")]
        [NoLoggingForUndoAttribute]
#if !DEBUG
        [DisableNullChecks]
        [DisableBoundsChecks]
#endif // !DEBUG
        internal static void StartAtomic(StackHeight stackHeight) {
            VTable.Assert(!TryAllManager.DISABLE_HOUSEKEEPING);
            DebugPrint("start atomic (slow)\n");
            
            Thread currentThread = Thread.CurrentThread;
            if(currentThread.tryAllManager == null) {
                currentThread.tryAllManager = new TryAllManager();
            }
            currentThread.tryAllManager.startTryAllHelper(true /*atomic*/,
                                                          stackHeight);
        }

        [RequiredByBartok("AtomicSupport")]
        [NoLoggingForUndoAttribute]
#if !DEBUG
        [DisableNullChecks]
        [DisableBoundsChecks]
#endif // !DEBUG
        internal static void StartAtomic(StackHeight stackHeight, 
                                         TryAllManager m) {
            VTable.Assert(!TryAllManager.DISABLE_HOUSEKEEPING);
            DebugPrint("start (quick)\n");

            // We may receive a null TryAllManager if this is the first
            // call to StartTryAll made by this thread.  NB, Start/Commit/Abort
            // "may mutate existing storage" in Operator.cs, so subsequent
            // calls will re-read the TryAllManager after we've stored it
            // in the Thread structure.  
            if (m == null) {
                StartAtomic(stackHeight);
            } else {
                m.startTryAllHelper(true /*atomic*/, stackHeight);
            }
        }

        [RequiredByBartok("TryAllSupport")]
        [NoLoggingForUndo]
#if !DEBUG
        [DisableNullChecks]
        [DisableBoundsChecks]
#endif // !DEBUG
        internal static void CommitTryAll() {
            VTable.Assert(!TryAllManager.DISABLE_HOUSEKEEPING);
            DebugPrint("commit try_all (slow)\n");

            TryAllManager.CurrentRunningTryAll.commitHelper(false /*tryall*/);
        }

        [RequiredByBartok("TryAllSupport")]
        [NoLoggingForUndo]
#if !DEBUG
        [DisableNullChecks]
        [DisableBoundsChecks]
#endif // !DEBUG
        internal static void CommitTryAll(TryAllManager m) {
            VTable.Assert(!TryAllManager.DISABLE_HOUSEKEEPING);
            DebugPrint("commit try_all (quick)\n");

            m.commitHelper(false /*tryall*/);
        }

        [RequiredByBartok("AtomicSupport")]
        [NoLoggingForUndo]
#if !DEBUG
        [DisableNullChecks]
        [DisableBoundsChecks]
#endif // !DEBUG
        internal static void CommitAtomic() {
            VTable.Assert(!TryAllManager.DISABLE_HOUSEKEEPING);
            DebugPrint("commit atomic (slow)\n");

            TryAllManager.CurrentRunningTryAll.commitHelper(true /*atomic*/);
        }

        [RequiredByBartok("AtomicSupport")]
        [NoLoggingForUndo]
#if !DEBUG
        [DisableNullChecks]
        [DisableBoundsChecks]
#endif // !DEBUG
        internal static void CommitAtomic(TryAllManager m) {
            VTable.Assert(!TryAllManager.DISABLE_HOUSEKEEPING);
            DebugPrint("commit atomic (quick)\n");

            m.commitHelper(true /*atomic*/);
        }

        [RequiredByBartok("TryAllSupport")]
        [NoLoggingForUndo]
        internal static void AbortTryAll() {
            VTable.Assert(!TryAllManager.DISABLE_HOUSEKEEPING);
            DebugPrint("abort try_all (slow)\n");

            TryAllManager.CurrentRunningTryAll.AbortHelper(false /*tryall*/);
        }

        [RequiredByBartok("TryAllSupport")]
        [NoLoggingForUndo]
        internal static void AbortTryAll(TryAllManager m) {
            VTable.Assert(!TryAllManager.DISABLE_HOUSEKEEPING);
            DebugPrint("abort try_all (quick)\n");
            m.AbortHelper(false /*tryall*/);
        }

        [RequiredByBartok("AtomicSupport")]
        [NoLoggingForUndo]
        internal static void AbortAtomic() {
            VTable.Assert(!TryAllManager.DISABLE_HOUSEKEEPING);
            DebugPrint("abort atomic (slow)\n");

            TryAllManager.CurrentRunningTryAll.AbortHelper(true /*atomic*/);
        }

        [RequiredByBartok("AtomicSupport")]
        [NoLoggingForUndo]
        internal static void AbortAtomic(TryAllManager m) {
            VTable.Assert(!TryAllManager.DISABLE_HOUSEKEEPING);
            DebugPrint("abort atomic (quick)\n");
            m.AbortHelper(true /*atomic*/);
        }

        [RequiredByBartok("AtomicSupport")]
        [NoLoggingForUndoAttribute]
        internal static void ValidateEnlistments() {
            VTable.Assert(!TryAllManager.DISABLE_HOUSEKEEPING);
            DebugPrint("ValidateEnlistments (slow)\n");
            TryAllManager.CurrentRunningTryAll.validateHelper();
        }

        [RequiredByBartok("AtomicSupport")]
        [NoLoggingForUndoAttribute]
        internal static void ValidateEnlistments(TryAllManager m) {
            VTable.Assert(!TryAllManager.DISABLE_HOUSEKEEPING);
            DebugPrint("ValidateEnlistments (quick)\n");
            m.validateHelper();
        }

        [RequiredByBartok("AtomicSupport")]
#if !DEBUG
        [DisableBoundsChecks]
        [DisableNullChecks]
#endif // !DEBUG
        internal static void EnsureLogMemoryForUpdateLog(uint bytesNeeded) {
            if (TryAllManager.DISABLE_ON_METHOD_ENTRY) {
                return;
            }
            TryAllManager m = TryAllManager.CurrentRunningTryAll;
            EnsureLogMemoryHelperForUpdateLog(bytesNeeded, m);
        }

        [RequiredByBartok("AtomicSupport")]
#if !DEBUG
        [DisableBoundsChecks]
        [DisableNullChecks]
#endif // !DEBUG
        internal static void EnsureLogMemoryForUpdateLog(uint bytesNeeded,
                                                         TryAllManager m) {
            if (TryAllManager.DISABLE_ON_METHOD_ENTRY) {
                return;
            }
            EnsureLogMemoryHelperForUpdateLog(bytesNeeded, m);
        }

        [RequiredByBartok("AtomicSupport")]
#if !DEBUG
        [DisableBoundsChecks]
        [DisableNullChecks]
#endif // !DEBUG
        internal static void EnsureLogMemoryForReadEnlistmentLog(uint bytesNeeded) {
            if (TryAllManager.DISABLE_ON_METHOD_ENTRY) {
                return;
            }
            TryAllManager m = TryAllManager.CurrentRunningTryAll;
            EnsureLogMemoryHelperForReadEnlistmentLog(bytesNeeded, m);
        }

        [RequiredByBartok("AtomicSupport")]
#if !DEBUG
        [DisableBoundsChecks]
        [DisableNullChecks]
#endif // !DEBUG
        internal static void EnsureLogMemoryForReadEnlistmentLog(uint bytesNeeded,
                                                                 TryAllManager m) {
            if (TryAllManager.DISABLE_ON_METHOD_ENTRY) {
                return;
            }
            EnsureLogMemoryHelperForReadEnlistmentLog(bytesNeeded, m);
        }

        [RequiredByBartok("AtomicSupport")]
#if !DEBUG
        [DisableBoundsChecks]
        [DisableNullChecks]
#endif // !DEBUG
        internal static void EnsureLogMemoryForUpdateEnlistmentLog(uint bytesNeeded) {
            if (TryAllManager.DISABLE_ON_METHOD_ENTRY) {
                return;
            }
            TryAllManager m = TryAllManager.CurrentRunningTryAll;
            EnsureLogMemoryHelperForUpdateEnlistmentLog(bytesNeeded, m);
        }

        [RequiredByBartok("AtomicSupport")]
#if !DEBUG
        [DisableBoundsChecks]
        [DisableNullChecks]
#endif // !DEBUG
        internal static void EnsureLogMemoryForUpdateEnlistmentLog(uint bytesNeeded,
                                                                   TryAllManager m) {
            if (TryAllManager.DISABLE_ON_METHOD_ENTRY) {
                return;
            }
            EnsureLogMemoryHelperForUpdateEnlistmentLog(bytesNeeded, m);
        }

        [RequiredByBartok("AtomicSupport")]
#if !DEBUG
        [DisableBoundsChecks]
        [DisableNullChecks]
#endif // !DEBUG
        internal static void EnlistObjForRead(Object obj) {
            if (TryAllManager.DISABLE_ON_METHOD_ENTRY) {
                return;
            }
            TryAllManager m = TryAllManager.CurrentRunningTryAll;
            EnlistObjHelperForRead(obj, m);
        }

        [RequiredByBartok("AtomicSupport")]
#if !DEBUG
        [DisableBoundsChecks]
        [DisableNullChecks]
#endif // !DEBUG
        internal static void EnlistObjForReadFast(Object obj) {
            if (TryAllManager.DISABLE_ON_METHOD_ENTRY) {
                return;
            }
            TryAllManager m = TryAllManager.CurrentRunningTryAll;
            EnlistObjHelperForReadFast(obj, m);
        }

        [RequiredByBartok("AtomicSupport")]
#if !DEBUG
        [DisableBoundsChecks]
        [DisableNullChecks]
#endif // !DEBUG
        internal static void EnlistObjForRead(Object obj, 
                                              TryAllManager m) {
            if (TryAllManager.DISABLE_ON_METHOD_ENTRY) {
                return;
            }
            EnlistObjHelperForRead(obj, m);
        }

        [RequiredByBartok("AtomicSupport")]
#if !DEBUG
        [DisableBoundsChecks]
        [DisableNullChecks]
#endif // !DEBUG
        internal static void EnlistObjForReadFast(Object obj, 
                                              TryAllManager m) {
            if (TryAllManager.DISABLE_ON_METHOD_ENTRY) {
                return;
            }
            EnlistObjHelperForReadFast(obj, m);
        }

        [RequiredByBartok("AtomicSupport")]
#if !DEBUG
        [DisableBoundsChecks]
        [DisableNullChecks]
#endif // !DEBUG
        internal static void EnlistAddrForRead(UIntPtr pobj) {
            if (TryAllManager.DISABLE_ON_METHOD_ENTRY) {
                return;
            }
            TryAllManager m = TryAllManager.CurrentRunningTryAll;
            EnlistAddrHelperForRead(pobj, m);
        }

        [RequiredByBartok("AtomicSupport")]
#if !DEBUG
        [DisableBoundsChecks]
        [DisableNullChecks]
#endif // !DEBUG
        internal static void EnlistAddrForReadFast(UIntPtr pobj) {
            if (TryAllManager.DISABLE_ON_METHOD_ENTRY) {
                return;
            }
            TryAllManager m = TryAllManager.CurrentRunningTryAll;
            EnlistAddrHelperForReadFast(pobj, m);
        }

        [RequiredByBartok("AtomicSupport")]
#if !DEBUG
        [DisableBoundsChecks]
        [DisableNullChecks]
#endif // !DEBUG
        internal static void EnlistAddrForRead(UIntPtr pobj, 
                                               TryAllManager m) {
            if (TryAllManager.DISABLE_ON_METHOD_ENTRY) {
                return;
            }
            EnlistAddrHelperForRead(pobj, m);
        }

        [RequiredByBartok("AtomicSupport")]
#if !DEBUG
        [DisableBoundsChecks]
        [DisableNullChecks]
#endif // !DEBUG
        internal static void EnlistAddrForReadFast(UIntPtr pobj, 
                                               TryAllManager m) {
            if (TryAllManager.DISABLE_ON_METHOD_ENTRY) {
                return;
            }
            EnlistAddrHelperForReadFast(pobj, m);
        }

        [RequiredByBartok("AtomicSupport")]
#if !DEBUG
        [DisableBoundsChecks]
        [DisableNullChecks]
#endif // !DEBUG
        internal static void EnlistIndirectForRead(UIntPtr ptr, 
                                                   UIntPtr byteSize) {
            if (TryAllManager.DISABLE_ON_METHOD_ENTRY) {
                return;
            }
            TryAllManager m = TryAllManager.CurrentRunningTryAll;
            EnlistIndirectHelper(ptr, byteSize, m, true);
        }

        [RequiredByBartok("AtomicSupport")]
#if !DEBUG
        [DisableBoundsChecks]
        [DisableNullChecks]
#endif // !DEBUG
        internal static void EnlistIndirectForReadFast(UIntPtr ptr, 
                                                       UIntPtr byteSize) {
            if (TryAllManager.DISABLE_ON_METHOD_ENTRY) {
                return;
            }
            TryAllManager m = TryAllManager.CurrentRunningTryAll;
            EnlistIndirectHelperFast(ptr, byteSize, m, true);
        }

        [RequiredByBartok("AtomicSupport")]
#if !DEBUG
        [DisableBoundsChecks]
        [DisableNullChecks]
#endif // !DEBUG
        internal static void EnlistIndirectForRead(UIntPtr ptr, 
                                                   UIntPtr byteSize, 
                                                   TryAllManager m) {
            if (TryAllManager.DISABLE_ON_METHOD_ENTRY) {
                return;
            }
            EnlistIndirectHelper(ptr, byteSize, m, true);
        }

        [RequiredByBartok("AtomicSupport")]
#if !DEBUG
        [DisableBoundsChecks]
        [DisableNullChecks]
#endif // !DEBUG
        internal static void EnlistIndirectForReadFast(UIntPtr ptr, 
                                                   UIntPtr byteSize, 
                                                   TryAllManager m) {
            if (TryAllManager.DISABLE_ON_METHOD_ENTRY) {
                return;
            }
            EnlistIndirectHelperFast(ptr, byteSize, m, true);
        }

        [RequiredByBartok("AtomicSupport")]
#if !DEBUG
        [DisableBoundsChecks]
        [DisableNullChecks]
#endif // !DEBUG
        internal static void EnlistObjForUpdate(Object obj) {
            if (TryAllManager.DISABLE_ON_METHOD_ENTRY) {
                return;
            }
            TryAllManager m = TryAllManager.CurrentRunningTryAll;
            EnlistObjHelperForUpdate(obj, m);
        }

        [RequiredByBartok("AtomicSupport")]
#if !DEBUG
        [DisableBoundsChecks]
        [DisableNullChecks]
#endif // !DEBUG
        internal static void EnlistObjForUpdateFast(Object obj) {
            if (TryAllManager.DISABLE_ON_METHOD_ENTRY) {
                return;
            }
            TryAllManager m = TryAllManager.CurrentRunningTryAll;
            EnlistObjHelperForUpdateFast(obj, m);
        }

        [RequiredByBartok("AtomicSupport")]
#if !DEBUG
        [DisableBoundsChecks]
        [DisableNullChecks]
#endif // !DEBUG
        internal static void EnlistObjForUpdate(Object obj, 
                                                TryAllManager m) {
            if (TryAllManager.DISABLE_ON_METHOD_ENTRY) {
                return;
            }
            EnlistObjHelperForUpdate(obj, m);
        }

        [RequiredByBartok("AtomicSupport")]
#if !DEBUG
        [DisableBoundsChecks]
        [DisableNullChecks]
#endif // !DEBUG
        internal static void EnlistObjForUpdateFast(Object obj, 
                                                    TryAllManager m) {
            if (TryAllManager.DISABLE_ON_METHOD_ENTRY) {
                return;
            }
            EnlistObjHelperForUpdateFast(obj, m);
        }

        [RequiredByBartok("AtomicSupport")]
#if !DEBUG
        [DisableBoundsChecks]
        [DisableNullChecks]
#endif // !DEBUG
        internal static void EnlistNewObjForUpdate(Object obj) {
            if (TryAllManager.DISABLE_ON_METHOD_ENTRY) {
                return;
            }
            TryAllManager m = TryAllManager.CurrentRunningTryAll;
            EnlistNewObjHelperForUpdate(obj, m);
        }

        [RequiredByBartok("AtomicSupport")]
#if !DEBUG
        [DisableBoundsChecks]
        [DisableNullChecks]
#endif // !DEBUG
        internal static void EnlistNewObjForUpdateFast(Object obj) {
            if (TryAllManager.DISABLE_ON_METHOD_ENTRY) {
                return;
            }
            TryAllManager m = TryAllManager.CurrentRunningTryAll;
            EnlistNewObjHelperForUpdateFast(obj, m);
        }

        [RequiredByBartok("AtomicSupport")]
#if !DEBUG
        [DisableBoundsChecks]
        [DisableNullChecks]
#endif // !DEBUG
        internal static void EnlistNewObjForUpdate(Object obj, 
                                                   TryAllManager m) {
            if (TryAllManager.DISABLE_ON_METHOD_ENTRY) {
                return;
            }
            EnlistNewObjHelperForUpdate(obj, m);
        }

        [RequiredByBartok("AtomicSupport")]

#if !DEBUG
        [DisableBoundsChecks]
        [DisableNullChecks]
#endif // !DEBUG
        internal static void EnlistNewObjForUpdateFast(Object obj, 
                                                       TryAllManager m) {
            if (TryAllManager.DISABLE_ON_METHOD_ENTRY) {
                return;
            }
            EnlistNewObjHelperForUpdateFast(obj, m);
        }

        [RequiredByBartok("AtomicSupport")]
#if !DEBUG
        [DisableBoundsChecks]
        [DisableNullChecks]
#endif // !DEBUG
        internal static void EnlistAddrForUpdate(UIntPtr pobj) {
            if (TryAllManager.DISABLE_ON_METHOD_ENTRY) {
                return;
            }
            TryAllManager m = TryAllManager.CurrentRunningTryAll;
            EnlistAddrHelperForUpdate(pobj, m);
        }

        [RequiredByBartok("AtomicSupport")]
#if !DEBUG
        [DisableBoundsChecks]
        [DisableNullChecks]
#endif // !DEBUG
        internal static void EnlistAddrForUpdateFast(UIntPtr pobj) {
            if (TryAllManager.DISABLE_ON_METHOD_ENTRY) {
                return;
            }
            TryAllManager m = TryAllManager.CurrentRunningTryAll;
            EnlistAddrHelperForUpdateFast(pobj, m);
        }

        [RequiredByBartok("AtomicSupport")]
#if !DEBUG
        [DisableBoundsChecks]
        [DisableNullChecks]
#endif // !DEBUG
        internal static void EnlistAddrForUpdate(UIntPtr pobj, 
                                                 TryAllManager m) {
            if (TryAllManager.DISABLE_ON_METHOD_ENTRY) {
                return;
            }
            EnlistAddrHelperForUpdate(pobj, m);
        }

        [RequiredByBartok("AtomicSupport")]
#if !DEBUG
        [DisableBoundsChecks]
        [DisableNullChecks]
#endif // !DEBUG
        internal static void EnlistAddrForUpdateFast(UIntPtr pobj, 
                                                     TryAllManager m) {
            if (TryAllManager.DISABLE_ON_METHOD_ENTRY) {
                return;
            }
            EnlistAddrHelperForUpdateFast(pobj, m);
        }

        [RequiredByBartok("AtomicSupport")]
#if !DEBUG
        [DisableBoundsChecks]
        [DisableNullChecks]
#endif // !DEBUG
        internal static void EnlistIndirectForUpdate(UIntPtr ptr, 
                                                     UIntPtr byteSize) {
            if (TryAllManager.DISABLE_ON_METHOD_ENTRY) {
                return;
            }
            TryAllManager m = TryAllManager.CurrentRunningTryAll;
            EnlistIndirectHelper(ptr, byteSize, m, false);
        }

        [RequiredByBartok("AtomicSupport")]
#if !DEBUG
        [DisableBoundsChecks]
        [DisableNullChecks]
#endif // !DEBUG
        internal static void EnlistIndirectForUpdateFast(UIntPtr ptr, 
                                                     UIntPtr byteSize) {
            if (TryAllManager.DISABLE_ON_METHOD_ENTRY) {
                return;
            }
            TryAllManager m = TryAllManager.CurrentRunningTryAll;
            EnlistIndirectHelperFast(ptr, byteSize, m, false);
        }

        [RequiredByBartok("AtomicSupport")]
#if !DEBUG
        [DisableBoundsChecks]
        [DisableNullChecks]
#endif // !DEBUG
        internal static void EnlistIndirectForUpdate(UIntPtr ptr, 
                                                     UIntPtr byteSize, 
                                                     TryAllManager m) {
            if (TryAllManager.DISABLE_ON_METHOD_ENTRY) {
                return;
            }
            EnlistIndirectHelper(ptr, byteSize, m, false);
        }

        [RequiredByBartok("AtomicSupport")]
#if !DEBUG
        [DisableBoundsChecks]
        [DisableNullChecks]
#endif // !DEBUG
        internal static void EnlistIndirectForUpdateFast(UIntPtr ptr, 
                                                     UIntPtr byteSize, 
                                                     TryAllManager m) {
            if (TryAllManager.DISABLE_ON_METHOD_ENTRY) {
                return;
            }
            EnlistIndirectHelperFast(ptr, byteSize, m, false);
        }

        [Inline]
#if !DEBUG
        [DisableBoundsChecks]
        [DisableNullChecks]
#endif // !DEBUG
        internal static void EnlistIndirectHelper(UIntPtr ptr, 
                                                  UIntPtr byteSize,
                                                  TryAllManager m,
                                                  bool readOnly) {
            UIntPtr startBlock = alignStart(ptr);

            if (readOnly) {
                m.tryAllCounters.IncrementEnlistIndirectForRead();
            } else {
                m.tryAllCounters.IncrementEnlistIndirectForUpdate();
            }

            if (isStack(startBlock)) {
                // Ptr to the stack : thread private so no need to enlist
                DebugPrint("Address {0} is on stack: no need to enlist\n",
                           __arglist((int)ptr));

            } else if (isStatic(startBlock)) {
                // Ptr to a static : enlist all blocks covered by the static

                UIntPtr endBlock = alignEnd(ptr + byteSize);

                DebugPrint("Address {0} is static, enlisting blocks {1}..{2}\n",
                           __arglist((int)ptr,
                                     (int)startBlock,
                                     (int)endBlock));

                for (UIntPtr i = startBlock ; i < endBlock ; i += blockSize) {
                    if (readOnly) {
                        EnlistAddrHelperForRead(i, m);
                    } else {
                        EnlistAddrHelperForUpdate(i, m);
                    }
                }

            } else {
                // Ptr to the heap : map to object pointer and enlist the object
                
                FactoredPointer factoredPointer = fixupInterior(ptr);
                Object obj = factoredPointer.baseObj;

                if (readOnly) {
                    EnlistObjForRead(obj, m);
                } else {
                    EnlistObjForUpdate(obj, m);
                }
            }
        }

        [Inline]
#if !DEBUG
        [DisableBoundsChecks]
        [DisableNullChecks]
#endif // !DEBUG
        internal static void EnlistIndirectHelperFast(UIntPtr ptr, 
                                                  UIntPtr byteSize,
                                                  TryAllManager m,
                                                  bool readOnly) {
            if (TryAllManager.DISABLE_ON_METHOD_ENTRY) {
                return;
            }
            UIntPtr startBlock = alignStart(ptr);

            if (readOnly) {
                m.tryAllCounters.IncrementEnlistIndirectForReadFast();
            } else {
                m.tryAllCounters.IncrementEnlistIndirectForUpdateFast();
            }

            if (isStack(startBlock)) {
                // Ptr to the stack : thread private so no need to enlist
                DebugPrint("Address {0} is on stack: no need to enlist\n",
                           __arglist((int)ptr));

            } else if (isStatic(startBlock)) {
                // Ptr to a static : enlist all blocks covered by the static

                UIntPtr endBlock = alignEnd(ptr + byteSize);

                DebugPrint("Address {0} is static, enlisting blocks {1}..{2}\n",
                           __arglist((int)ptr,
                                     (int)startBlock,
                                     (int)endBlock));

                for (UIntPtr i = startBlock ; i < endBlock ; i += blockSize) {
                    if (readOnly) {
                        EnlistAddrHelperForReadFast(i, m);
                    } else {
                        EnlistAddrHelperForUpdateFast(i, m);
                    }
                }

            } else {
                // Ptr to the heap : map to object pointer and enlist the object
                
                FactoredPointer factoredPointer = fixupInterior(ptr);
                Object obj = factoredPointer.baseObj;

                if (readOnly) {
                    EnlistObjForReadFast(obj, m);
                } else {
                    EnlistObjForUpdateFast(obj, m);
                }
            }
        }

        [RequiredByBartok("TryAllSupport")]
#if !DEBUG
        [DisableBoundsChecks]
        [DisableNullChecks]
#endif // !DEBUG
        internal static void LogValHeapMultiple(Object obj, 
                                                UIntPtr off,
                                                UIntPtr size) {
            if (TryAllManager.DISABLE_ON_METHOD_ENTRY) {
                return;
            }
            TryAllManager m = TryAllManager.CurrentRunningTryAll;
            LogValHeapMultipleHelper(obj, off, size, m);
        }

        [RequiredByBartok("TryAllSupport")]
#if !DEBUG
        [DisableBoundsChecks]
        [DisableNullChecks]
#endif // !DEBUG
        internal static void LogValHeapMultipleFast(Object obj, 
                                                    UIntPtr off,
                                                    UIntPtr size) {
            if (TryAllManager.DISABLE_ON_METHOD_ENTRY) {
                return;
            }
            TryAllManager m = TryAllManager.CurrentRunningTryAll;
            LogValHeapMultipleHelperFast(obj, off, size, m);
        }

        [RequiredByBartok("TryAllSupport")]
#if !DEBUG
        [DisableBoundsChecks]
        [DisableNullChecks]
#endif // !DEBUG
        internal static void LogValHeapMultiple(Object obj,
                                                UIntPtr off, 
                                                UIntPtr size, 
                                                TryAllManager m) {
            if (TryAllManager.DISABLE_ON_METHOD_ENTRY) {
                return;
            }
            LogValHeapMultipleHelper(obj, off, size, m);
        }

        [RequiredByBartok("TryAllSupport")]
#if !DEBUG
        [DisableBoundsChecks]
        [DisableNullChecks]
#endif // !DEBUG
        internal static void LogValHeapMultipleFast(Object obj,
                                                    UIntPtr off, 
                                                    UIntPtr size, 
                                                    TryAllManager m) {
            if (TryAllManager.DISABLE_ON_METHOD_ENTRY) {
                return;
            }
            LogValHeapMultipleHelperFast(obj, off, size, m);
        }

        [Inline]
#if !DEBUG
        [DisableBoundsChecks]
        [DisableNullChecks]
#endif // !DEBUG
        private static void LogValHeapMultipleHelper(Object obj, 
                                                     UIntPtr off, 
                                                     UIntPtr size, 
                                                     TryAllManager m) {

            UIntPtr offset = off;
            UIntPtr startOffset = offset & blockAlignmentNegMask;
            UIntPtr endOffset = offset + size;
            if((endOffset & blockAlignmentMask) != 0) {
                endOffset += blockSize;
                endOffset &= blockAlignmentNegMask;
            }

            DebugPrint("<TryAll> log::vm: {0}/{1}+{2}::{3}--{4}\n", 
                       __arglist((uint)Magic.addressOf(obj),
                                 (uint)offset,
                                 (uint)size,
                                 (uint)startOffset,
                                 (uint)endOffset));


            m.tryAllCounters.IncrementLogValHeapMultiple();

            for(UIntPtr curOffset = startOffset;
                curOffset < endOffset;
                curOffset += blockSize) {

                LogValHeapHelper(obj, curOffset, m);
            }
        }

        [Inline]
#if !DEBUG
        [DisableBoundsChecks]
        [DisableNullChecks]
#endif // !DEBUG
        private static void LogValHeapMultipleHelperFast(Object obj, 
                                                         UIntPtr off, 
                                                         UIntPtr size, 
                                                         TryAllManager m) {

            UIntPtr offset = off;
            UIntPtr startOffset = offset & blockAlignmentNegMask;
            UIntPtr endOffset = offset + size;
            if((endOffset & blockAlignmentMask) != 0) {
                endOffset += blockSize;
                endOffset &= blockAlignmentNegMask;
            }

            DebugPrint("<TryAll> log::vm: {0}/{1}+{2}::{3}--{4}\n", 
                       __arglist((uint)Magic.addressOf(obj),
                                 (uint)offset,
                                 (uint)size,
                                 (uint)startOffset,
                                 (uint)endOffset));


            m.tryAllCounters.IncrementLogValHeapMultipleFast();

            for(UIntPtr curOffset = startOffset;
                curOffset < endOffset;
                curOffset += blockSize) {

                LogValHeapHelperFast(obj, curOffset, m);
            }
        }

        [RequiredByBartok("TryAllSupport")]
#if !DEBUG
        [DisableBoundsChecks]
        [DisableNullChecks]
#endif // !DEBUG
        internal static void LogValHeap(Object obj, 
                                        UIntPtr off) {
            if (TryAllManager.DISABLE_ON_METHOD_ENTRY) {
                return;
            }
            TryAllManager m = TryAllManager.CurrentRunningTryAll;
            LogValHeapHelper(obj, off, m);
        }

        [RequiredByBartok("TryAllSupport")]
#if !DEBUG
        [DisableBoundsChecks]
        [DisableNullChecks]
#endif // !DEBUG
        internal static void LogValHeapFast(Object obj, 
                                        UIntPtr off) {
            if (TryAllManager.DISABLE_ON_METHOD_ENTRY) {
                return;
            }
            TryAllManager m = TryAllManager.CurrentRunningTryAll;
            LogValHeapHelperFast(obj, off, m);
        }

        [RequiredByBartok("TryAllSupport")]
#if !DEBUG
        [DisableBoundsChecks]
        [DisableNullChecks]
#endif // !DEBUG
        internal static void LogValHeap(Object obj, 
                                        UIntPtr off,
                                        TryAllManager m) {
            if (TryAllManager.DISABLE_ON_METHOD_ENTRY) {
                return;
            }
            LogValHeapHelper(obj, off, m);
        }

        [RequiredByBartok("TryAllSupport")]
#if !DEBUG
        [DisableBoundsChecks]
        [DisableNullChecks]
#endif // !DEBUG
        internal static void LogValHeapFast(Object obj, 
                                            UIntPtr off,
                                            TryAllManager m) {
            if (TryAllManager.DISABLE_ON_METHOD_ENTRY) {
                return;
            }
            LogValHeapHelperFast(obj, off, m);
        }

        [RequiredByBartok("TryAllSupport")]
#if !DEBUG
        [DisableBoundsChecks]
        [DisableNullChecks]
#endif // !DEBUG
        internal static void LogValStatic(UIntPtr addr) {
            if (TryAllManager.DISABLE_ON_METHOD_ENTRY) {
                return;
            }
            TryAllManager m = TryAllManager.CurrentRunningTryAll;
            LogValStaticHelper(addr, m);
        }

        [RequiredByBartok("TryAllSupport")]
#if !DEBUG
        [DisableBoundsChecks]
        [DisableNullChecks]
#endif // !DEBUG
        internal static void LogValStaticFast(UIntPtr addr) {
            if (TryAllManager.DISABLE_ON_METHOD_ENTRY) {
                return;
            }
            TryAllManager m = TryAllManager.CurrentRunningTryAll;
            LogValStaticHelperFast(addr, m);
        }

        [RequiredByBartok("TryAllSupport")]
#if !DEBUG
        [DisableBoundsChecks]
        [DisableNullChecks]
#endif // !DEBUG
        internal static void LogValStatic(UIntPtr addr,
                                          TryAllManager m) {
            if (TryAllManager.DISABLE_ON_METHOD_ENTRY) {
                return;
            }
            LogValStaticHelper(addr, m);
        }

        [RequiredByBartok("TryAllSupport")]
#if !DEBUG
        [DisableBoundsChecks]
        [DisableNullChecks]
#endif // !DEBUG
        internal static void LogValStaticFast(UIntPtr addr,
                                              TryAllManager m) {
            if (TryAllManager.DISABLE_ON_METHOD_ENTRY) {
                return;
            }
            LogValStaticHelperFast(addr, m);
        }

        // This function assumes that off is already 4/8byte aligned.
        [RequiredByBartok("TryAllSupport")]
#if !DEBUG
        [DisableBoundsChecks]
        [DisableNullChecks]
#endif // !DEBUG
        internal static void LogRefHeap(Object obj, 
                                        UIntPtr off) {
            if (TryAllManager.DISABLE_ON_METHOD_ENTRY) {
                return;
            }
            TryAllManager m = TryAllManager.CurrentRunningTryAll;
            LogRefHeapHelper(obj, off, m);
        }

        [RequiredByBartok("TryAllSupport")]
#if !DEBUG
        [DisableBoundsChecks]
        [DisableNullChecks]
#endif // !DEBUG
        internal static void LogRefStatic(UIntPtr addr) {
            if (TryAllManager.DISABLE_ON_METHOD_ENTRY) {
                return;
            }
            TryAllManager m = TryAllManager.CurrentRunningTryAll;
            LogRefStaticHelper(addr, m);
        }

        // This function assumes that off is already 4/8byte aligned.
        [RequiredByBartok("TryAllSupport")]
#if !DEBUG
        [DisableBoundsChecks]
        [DisableNullChecks]
#endif // !DEBUG
        internal static void LogRefHeapFast(Object obj, 
                                            UIntPtr off) {
            if (TryAllManager.DISABLE_ON_METHOD_ENTRY) {
                return;
            }
            TryAllManager m = TryAllManager.CurrentRunningTryAll;
            LogRefHeapHelperFast(obj, off, m);
        }

        [RequiredByBartok("TryAllSupport")]
#if !DEBUG
        [DisableBoundsChecks]
        [DisableNullChecks]
#endif // !DEBUG
        internal static void LogRefStaticFast(UIntPtr addr) {
            if (TryAllManager.DISABLE_ON_METHOD_ENTRY) {
                return;
            }
            TryAllManager m = TryAllManager.CurrentRunningTryAll;
            LogRefStaticHelperFast(addr, m);
        }

        // This function assumes that off is already 4/8byte aligned.
        [RequiredByBartok("TryAllSupport")]
#if !DEBUG
        [DisableBoundsChecks]
        [DisableNullChecks]
#endif // !DEBUG
        internal static void LogRefHeap(Object obj, 
                                        UIntPtr off,
                                        TryAllManager m) {
            if (TryAllManager.DISABLE_ON_METHOD_ENTRY) {
                return;
            }
            LogRefHeapHelper(obj, off, m);
        }

        [RequiredByBartok("TryAllSupport")]
#if !DEBUG
        [DisableBoundsChecks]
        [DisableNullChecks]
#endif // !DEBUG
        internal static void LogRefStatic(UIntPtr addr,
                                          TryAllManager m) {
            if (TryAllManager.DISABLE_ON_METHOD_ENTRY) {
                return;
            }
            LogRefStaticHelper(addr, m);
        }

        // This function assumes that off is already 4/8byte aligned.
        [RequiredByBartok("TryAllSupport")]
#if !DEBUG
        [DisableBoundsChecks]
        [DisableNullChecks]
#endif // !DEBUG
        internal static void LogRefHeapFast(Object obj, 
                                            UIntPtr off,
                                            TryAllManager m) {
            if (TryAllManager.DISABLE_ON_METHOD_ENTRY) {
                return;
            }
            LogRefHeapHelperFast(obj, off, m);
        }

        [RequiredByBartok("TryAllSupport")]
#if !DEBUG
        [DisableBoundsChecks]
        [DisableNullChecks]
#endif // !DEBUG
        internal static void LogRefStaticFast(UIntPtr addr,
                                              TryAllManager m) {
            if (TryAllManager.DISABLE_ON_METHOD_ENTRY) {
                return;
            }
            LogRefStaticHelperFast(addr, m);
        }

        // This function assumes that pobj is already 4/8byte aligned.
        [RequiredByBartok("TryAllSupport")]
#if !DEBUG
        [DisableBoundsChecks]
        [DisableNullChecks]
#endif // !DEBUG
        internal static void LogIndirectRef(UIntPtr pobj) {
            if (TryAllManager.DISABLE_ON_METHOD_ENTRY) {
                return;
            }
            TryAllManager m = TryAllManager.CurrentRunningTryAll;
            LogIndirectRefHelper(pobj, m);
        }

       // This function assumes that pobj is already 4/8byte aligned.
        [RequiredByBartok("TryAllSupport")]
#if !DEBUG
        [DisableBoundsChecks]
        [DisableNullChecks]
#endif // !DEBUG
        internal static void LogIndirectRefFast(UIntPtr pobj) {
            if (TryAllManager.DISABLE_ON_METHOD_ENTRY) {
                return;
            }
            TryAllManager m = TryAllManager.CurrentRunningTryAll;
            LogIndirectRefHelperFast(pobj, m);
        }

        // This function assumes that pobj is already 4/8byte aligned.
        [RequiredByBartok("TryAllSupport")]
#if !DEBUG
        [DisableBoundsChecks]
        [DisableNullChecks]
#endif // !DEBUG
        internal static void LogIndirectRef(UIntPtr pobj, 
                                            TryAllManager m) {
            if (TryAllManager.DISABLE_ON_METHOD_ENTRY) {
                return;
            }
            LogIndirectRefHelper(pobj, m);
        }

        // This function assumes that pobj is already 4/8byte aligned.
        [RequiredByBartok("TryAllSupport")]
#if !DEBUG
        [DisableBoundsChecks]
        [DisableNullChecks]
#endif // !DEBUG
        internal static void LogIndirectRefFast(UIntPtr pobj, 
                                            TryAllManager m) {
            if (TryAllManager.DISABLE_ON_METHOD_ENTRY) {
                return;
            }
            LogIndirectRefHelperFast(pobj, m);
        }

        // This function assumes that pobj is already 4/8byte aligned.
        [Inline]
#if !DEBUG
        [DisableBoundsChecks]
        [DisableNullChecks]
#endif // !DEBUG
        internal static void LogIndirectRefHelper(UIntPtr pobj,
                                                  TryAllManager m) {
            if(isStack(pobj)) {
                LogIndirectRefStackHelper(pobj, m);
            } else {
                LogIndirectRefHeapHelper(pobj, m);
            }
        }

        // This function assumes that pobj is already 4/8byte aligned.
        [Inline]
#if !DEBUG
        [DisableBoundsChecks]
        [DisableNullChecks]
#endif // !DEBUG
        internal static void LogIndirectRefHelperFast(UIntPtr pobj,
                                                  TryAllManager m) {
            if(isStack(pobj)) {
                LogIndirectRefStackHelperFast(pobj, m);
            } else {
                LogIndirectRefHeapHelperFast(pobj, m);
            }
        }
        
        // pobj does not have to be aligned
        [RequiredByBartok("TryAllSupport")]
#if !DEBUG
        [DisableBoundsChecks]
        [DisableNullChecks]
#endif // !DEBUG
        internal static void LogIndirectValMultiple(UIntPtr pobj, 
                                                    UIntPtr size) {
            if (TryAllManager.DISABLE_ON_METHOD_ENTRY) {
                return;
            }
            TryAllManager m = TryAllManager.CurrentRunningTryAll;
            LogIndirectValMultipleHelper(pobj, size, m);
        }

        // pobj does not have to be aligned
        [RequiredByBartok("TryAllSupport")]
#if !DEBUG
        [DisableBoundsChecks]
        [DisableNullChecks]
#endif // !DEBUG
        internal static void LogIndirectValMultipleFast(UIntPtr pobj, 
                                                        UIntPtr size) {
            if (TryAllManager.DISABLE_ON_METHOD_ENTRY) {
                return;
            }
            TryAllManager m = TryAllManager.CurrentRunningTryAll;
            LogIndirectValMultipleHelperFast(pobj, size, m);
        }

        // pobj does not have to be aligned
        [RequiredByBartok("TryAllSupport")]
#if !DEBUG
        [DisableBoundsChecks]
        [DisableNullChecks]
#endif // !DEBUG
        internal static void LogIndirectValMultiple(UIntPtr pobj, 
                                                    UIntPtr size,
                                                    TryAllManager m) {
            if (TryAllManager.DISABLE_ON_METHOD_ENTRY) {
                return;
            }
            LogIndirectValMultipleHelper(pobj, size, m);
        }

        // pobj does not have to be aligned
        [RequiredByBartok("TryAllSupport")]
#if !DEBUG
        [DisableBoundsChecks]
        [DisableNullChecks]
#endif // !DEBUG
        internal static void LogIndirectValMultipleFast(UIntPtr pobj, 
                                                        UIntPtr size,
                                                        TryAllManager m) {
            if (TryAllManager.DISABLE_ON_METHOD_ENTRY) {
                return;
            }
            LogIndirectValMultipleHelperFast(pobj, size, m);
        }

        [Inline]
#if !DEBUG
        [DisableBoundsChecks]
        [DisableNullChecks]
#endif // !DEBUG
        private static void LogIndirectValMultipleHelper(UIntPtr pobj, 
                                                         UIntPtr size, 
                                                         TryAllManager m) {
            UIntPtr mem = pobj;
            UIntPtr startBlock = alignStart(mem);
            UIntPtr endBlock = alignEnd(mem + size);
            
            DebugPrint("<TryAll> logi::vm: {0}+{1}::{2}--{3}\n", 
                       __arglist((uint)pobj,
                                 (uint)size,
                                 (uint)startBlock,
                                 (uint)endBlock));


            m.tryAllCounters.IncrementLogIndirectValMultiple();
            
            bool isstack = isStack(startBlock);
            
            Object startBlock2 = Magic.fromAddress(startBlock);
            Object endBlock2 = Magic.fromAddress(endBlock);
            
            // REVIEW: Using Object to represent interior pointers
            for(Object block = startBlock2;
                Magic.addressOf(block) < Magic.addressOf(endBlock2);
                block = Magic.fromAddress(Magic.addressOf(block) + blockSize)) {
                if(isstack) {
                    LogIndirectValStackHelper(Magic.addressOf(block), m);
                } else {
                    LogIndirectValHeapHelper(Magic.addressOf(block), m);
                }
            }
        }

        [Inline]
#if !DEBUG
        [DisableBoundsChecks]
        [DisableNullChecks]
#endif // !DEBUG
        private static void LogIndirectValMultipleHelperFast(UIntPtr pobj, 
                                                         UIntPtr size, 
                                                         TryAllManager m) {
            UIntPtr mem = pobj;
            UIntPtr startBlock = alignStart(mem);
            UIntPtr endBlock = alignEnd(mem + size);
            
            DebugPrint("<TryAll> logi::vm: {0}+{1}::{2}--{3}\n", 
                       __arglist((uint)pobj,
                                 (uint)size,
                                 (uint)startBlock,
                                 (uint)endBlock));


            m.tryAllCounters.IncrementLogIndirectValMultipleFast();
            
            bool isstack = isStack(startBlock);
            
            Object startBlock2 = Magic.fromAddress(startBlock);
            Object endBlock2 = Magic.fromAddress(endBlock);
            
            // REVIEW: Using Object to represent interior pointers
            for(Object block = startBlock2;
                Magic.addressOf(block) < Magic.addressOf(endBlock2);
                block = Magic.fromAddress(Magic.addressOf(block) + blockSize)) {
                if(isstack) {
                    LogIndirectValStackHelperFast(Magic.addressOf(block), m);
                } else {
                    LogIndirectValHeapHelperFast(Magic.addressOf(block), m);
                }
            }
        }
        
        // This function assumes that pobj is already 4/8byte aligned.
        [RequiredByBartok("TryAllSupport")]
#if !DEBUG
        [DisableBoundsChecks]
        [DisableNullChecks]
#endif // !DEBUG
        internal static void LogIndirectVal(UIntPtr pobj) {
            if (TryAllManager.DISABLE_ON_METHOD_ENTRY) {
                return;
            }
            TryAllManager m = TryAllManager.CurrentRunningTryAll;
            LogIndirectValHelper(pobj, m);
        }

        // This function assumes that pobj is already 4/8byte aligned.
        [RequiredByBartok("TryAllSupport")]
#if !DEBUG
        [DisableBoundsChecks]
        [DisableNullChecks]
#endif // !DEBUG
        internal static void LogIndirectValFast(UIntPtr pobj) {
            if (TryAllManager.DISABLE_ON_METHOD_ENTRY) {
                return;
            }
            TryAllManager m = TryAllManager.CurrentRunningTryAll;
            LogIndirectValHelperFast(pobj, m);
        }
        
        // This function assumes that pobj is already 4/8byte aligned.
        [RequiredByBartok("TryAllSupport")]
#if !DEBUG
        [DisableBoundsChecks]
        [DisableNullChecks]
#endif // !DEBUG
        internal static void LogIndirectVal(UIntPtr pobj,
                                            TryAllManager m) {
            if (TryAllManager.DISABLE_ON_METHOD_ENTRY) {
                return;
            }
            LogIndirectValHelper(pobj, m);
        }

        // This function assumes that pobj is already 4/8byte aligned.
        [RequiredByBartok("TryAllSupport")]
#if !DEBUG
        [DisableBoundsChecks]
        [DisableNullChecks]
#endif // !DEBUG
        internal static void LogIndirectValFast(UIntPtr pobj,
                                                TryAllManager m) {
            if (TryAllManager.DISABLE_ON_METHOD_ENTRY) {
                return;
            }
            LogIndirectValHelperFast(pobj, m);
        }
        
        [Inline]
#if !DEBUG
        [DisableBoundsChecks]
        [DisableNullChecks]
#endif // !DEBUG
        private static void LogIndirectValHelper(UIntPtr pobj,
                                                 TryAllManager m) {
            if(isStack(pobj)) {
                LogIndirectValStackHelper(pobj, m);
            } else {
                LogIndirectValHeapHelper(pobj, m);
            }
        }

        [Inline]
#if !DEBUG
        [DisableBoundsChecks]
        [DisableNullChecks]
#endif // !DEBUG
        private static void LogIndirectValHelperFast(UIntPtr pobj,
                                                 TryAllManager m) {
            if(isStack(pobj)) {
                LogIndirectValStackHelperFast(pobj, m);
            } else {
                LogIndirectValHeapHelperFast(pobj, m);
            }
        }
        
        //----------------------------------------------------------------------
        //
        // Debugging & profiling
        //
        // ENABLE_TRACING causes messages through DebugPrint to be
        // output directly.  

        // DebugPrintNoLock is used when acquiring a lock is not a good idea.
        //

        [System.Diagnostics.Conditional("ENABLE_TRACING")]
        [NoInline]
        internal static void DebugPrint(String v)
        {
            LockDebugPrint();
            VTable.DebugPrint(v, new ArgIterator());
            UnlockDebugPrint();
        }

        [System.Diagnostics.Conditional("ENABLE_TRACING")]
        [NoInline]
        internal static void DebugPrint(String v, __arglist)
        {
            LockDebugPrint();
            VTable.DebugPrint(v, new ArgIterator(__arglist));
            UnlockDebugPrint();
        }

        [System.Diagnostics.Conditional("ENABLE_TRACING")]
        [NoInline]
        internal static void DebugPrintNoLock(String v, __arglist)
        {
            VTable.DebugPrint(v, new ArgIterator(__arglist));
        }

        [System.Diagnostics.Conditional("ENABLE_TRACING")]
        [NoInline]
        internal static void DebugPrintNoLock(String v)
        {
            VTable.DebugPrint(v, new ArgIterator());
        }

        [System.Diagnostics.Conditional("ENABLE_GC_TRACING")]
        [NoInline]
        internal static void DebugPrintGC(String v)
        {
            VTable.DebugPrint(v, new ArgIterator());
        }

        [System.Diagnostics.Conditional("ENABLE_GC_TRACING")]
        [NoInline]
        internal static void DebugPrintGC(String v, __arglist)
        {
            VTable.DebugPrint(v, new ArgIterator(__arglist));
        }

        // GC is currently co-operative so we must periodically check in if in a loop
        // without allocation, e.g. in LockDebugPrint.  We obviously don't need these 
        // counters to be precise, so no attempt at concurrency control.
        static volatile int i;
        static volatile Object o;
        static void CheckInForGCHack() {
            i++;
            if ((i & 65535) == 0) {
                o = new Object();
            }
        }

        static int daplock = 0; // 0 => unlocked

        [System.Diagnostics.Conditional("ENABLE_TRACING")]
        internal static void LockDebugPrint() {
            if (!DuringGC()) {
                while (Interlocked.CompareExchange(ref daplock,
                                                   1,
                                                   0) != 0) {
                    CheckInForGCHack();
                }
                DebugPrintNoLock("{0} : ", 
                                 __arglist(Thread.CurrentThread.threadIndex));
            }
        }

        [System.Diagnostics.Conditional("ENABLE_TRACING")]
        internal static void UnlockDebugPrint() {
            if (!DuringGC()) {
                daplock = 0;
            }
        }

        internal static void LockLock() {
            while (Interlocked.CompareExchange(ref daplock,
                                               1,
                                               0) != 0) {
                CheckInForGCHack();
            }
        }

        internal static void UnlockUnlock() {
            daplock = 0;
        }



#if ENABLE_TRACING
        static private bool duringGC = false;

        static bool DuringGC() {
            return duringGC;
        }

        static void SetDuringGC(bool f) {
            duringGC =  f;
        }
#else
        static bool DuringGC() {
            // Callers should be conditional on ENABLE_TRACING.
            VTable.NotReached("Testing DuringGC without ENABLE_TRACING set");
            return false;
        }

        static void SetDuringGC(bool f) {
            /* Nothing */
        }
#endif        

        //----------------------------------------------------------------------
        //
        // Shake debugging
        // 
        // If SHAKE is #defined then we periodically pretend to be invalid in order
        // to try to test more code paths.  
        // 
        // Each time we decide to shake we either (a) make sure the transaction
        // will appear invalid and then raise an ordinary exception, or (b)
        // raise AtomicIsInvalidException.  The first test ensures that we
        // correctly suppress exceptions leaking out of invalid transactions.
        // The second test deals with 'ordinary' invalidity, e.g. detected
        // part way through a commit.

        
        public sealed class ShakeException : Exception {}
    
        internal int shakeCtr = 0; 
        internal int shakeLim = 1;
        internal bool shakeWithExn = false;

        internal static void ShakeCurrent(bool duringGC) {
#if SHAKE
            CurrentRunningTryAll.Shake(duringGC);
#endif
        }

        internal bool Occasionally() {
            bool result = false;
#if SHAKE
            if ((shakeCtr++) % shakeLim == 0) {
                shakeLim += 10;//= 2;
                shakeCtr = 1;
                result = true;
            }
#endif
            return result;
        }

        internal void Shake(bool duringGC) {
#if SHAKE
            if (Occasionally()) {
                if (currentTryAllStatus == TryAllStatus.Invalid) {
                    DebugPrint("Already invalid\n");
                } else {
                    DebugPrint("Pretending to be invalid\n");
                    shakeWithExn = !shakeWithExn;
                    if (shakeWithExn && !duringGC) {
                        DebugPrint("Raising ShakeException\n");
                        tryAllCounters.IncrementInvalidShakeException();
                        tryAllCounters.IncrementInvalidOutsideGC();
                        currentTryAllStatus = TryAllStatus.Invalid;
                        throw new ShakeException();
                    } else {
                        tryAllCounters.IncrementInvalidShake();
                        becomeInvalid(duringGC);
                    }
                }
            }
#endif
        }

        //----------------------------------------------------------------------
        //
        // Debugging support.  
        //
        // These functions are for use from user code, e.g. to check that none of
        // the objects making up an application's data structure are enlisted
        // once a test has finished.

        public static void DebugAbort() {
#if DEBUG
            VTable.DebugBreak();
#endif
        }

        public static bool DebugIsQuiescent(Object obj) { 
            STMHandle h = new STMHandle(obj);
            STMSnapshot s = h.GetSTMSnapshot();
            STMWord w = s.GetSTMWord();
            bool r = w.IsQuiescent(); 
#if DEBUG
            if (!r) {
                DebugPrint("Not quiescent: {0} snapshot=<{1:x}> word=<{2:x}>\n", 
                           __arglist(Magic.addressOf(obj), s.value, w.value));
            }
#endif
            return r;
        }

        public static bool InTryAll {
            get {
                Thread currentThread = Thread.CurrentThread;
                if(currentThread.tryAllManager == null) {
                    return false;
                }
                TryAllManager manager = currentThread.tryAllManager;
                VTable.Deny(manager.nextSavedTryAll < 0,
                            "nextSavedTryAll < 0");
                return manager.nextSavedTryAll > 0;
            }
        }

        //----------------------------------------------------------------------
        //
        // Per-call-site profiling.
        //
        // If /TryAllPerCallSiteProfiling is enabled then Bartok will generate calls
        // to UnsafeSetCallSite just before each Enlist* or Log* instruction.  This
        // call supplies an integer value that uniquely identifies the call sit.
        //
        // The Enlist* and Log* operations are responsible for calling CountAsLogged
        // if they write to the log.  
        //
        // The counting is best effort because a single shared call site ID
        // is kept at runtime and shared count arrays are used.  This code is
        // intended for single-threaded use when developing optimizations to
        // reduce the calls made onto Enlist* and Log* functions.

#if ENABLE_PER_CALL_SITE_PROFILING
        private const int MAX_CALL_SITES_TRACKED = 16384;
        private static int[] totCount = new int[MAX_CALL_SITES_TRACKED];
        private static int[] logCount = new int[MAX_CALL_SITES_TRACKED];
        private static int lastCallSite = 0;

        [RequiredByBartok("TryAllSupport")]
        public static void UnsafeSetCallSite(int i) {
            lastCallSite = i;
            totCount[lastCallSite]++;
        }

        internal static void CountAsLogged() {
            logCount[lastCallSite]++;
        }

        internal static void DumpPerCallSiteStats() {
            for (int i = 0; i < totCount.Length; i++) {
                if (totCount[i] != 0) {
                    VTable.DebugPrint("Id {0} called {1} logged {2} ({3} %)\n",
                                      __arglist(i,
                                                totCount[i],
                                                logCount[i],
                                                (100*(long)logCount[i]) / totCount[i]));
                }
            }
        }
#else

        [RequiredByBartok("TryAllSupport")]
        public static void UnsafeSetCallSite(int i) {
            /* Nothing */
        }

        internal static void CountAsLogged() {
            /* Nothing */
        }

        internal static void DumpPerCallSiteStats() {
            /* Nothing */
        }
#endif

        //----------------------------------------------------------------------
        //
        // Utility functions used during roll-back for distinguishing different
        // kinds of address and making updates.

        private static bool isStack(UIntPtr addr) {
            PageType pageType = PageTable.Type(PageTable.Page(addr));
            VTable.Deny(pageType == PageType.System,
                        "pageType == PageType.System");
            return pageType == PageType.Stack;
        }

        private static bool isStatic(UIntPtr addr) {
            PageType pageType = PageTable.Type(PageTable.Page(addr));
            VTable.Deny(pageType == PageType.System,
                        "pageType == PageType.System");
            return pageType == PageType.NonGC;
        }

        private static bool isNative(UIntPtr addr) {
            PageType pageType = PageTable.Type(PageTable.Page(addr));
            VTable.Deny(pageType == PageType.System,
                        "pageType == PageType.System");
            return pageType == PageType.Unallocated;
        }

        private static bool isGcHeap(UIntPtr addr) {
            VTable.Deny(PageTable.Type(PageTable.Page(addr))
                        == PageType.System,
                        "pageType == PageType.System");
            return PageTable.IsGcPage(PageTable.Page(addr));
        }

        internal static unsafe UIntPtr *getLoc(Object obj, UIntPtr offset) {
            if(obj == null) {
                return enpointerize(offset);
            } else {
                return enpointerize((Magic.addressOf(obj)+offset));
            }

        }

        internal static unsafe void setAt(Object obj, UIntPtr offset,
                                          UIntPtr data) {

            DebugPrint("<TryAll> set::v: {0}/{1}::{2}->{3}\n", 
                       __arglist((uint)Magic.addressOf(obj),
                                 (uint)offset,
                                 (uint)(*(getLoc(obj,offset))),
                                 (uint)data));

            Magic.SetAt(obj, offset, data);
        }

        internal static unsafe void setAt(Object obj, UIntPtr offset,
                                          Object data) {

            DebugPrint("<TryAll> set::r: {0}/{1}::{2}->{3}\n", 
                       __arglist((uint)Magic.addressOf(obj),
                                 (uint)offset,
                                 (uint)(*(getLoc(obj,offset))),
                                 (uint)Magic.addressOf(data)));

            Magic.SetAt(obj, offset, data);
        }

        internal static unsafe void setAtStack
        (StackHeight stackHeight, Object obj, UIntPtr offset, UIntPtr data) {
            UIntPtr *memLoc = getLoc(obj,offset);
            if(isStack((UIntPtr)memLoc)
               && StackHeight.Deeper(stackHeight, (StackHeight)(UIntPtr)memLoc)) {

                DebugPrint("<TryAll> set::vs: {0}/{1}::{2}->{3}\n",  
                           __arglist((uint)Magic.addressOf(obj),
                                     (uint)offset,
                                     (uint)(*(getLoc(obj,offset))),
                                     (uint)data));

                Magic.SetAt(obj, offset, data);
            }
        }

        internal static unsafe void setAtStack
        (StackHeight stackHeight, Object obj, UIntPtr offset, Object data) {
            UIntPtr *memLoc = getLoc(obj,offset);
            if(isStack((UIntPtr)memLoc)
               && StackHeight.Deeper(stackHeight, (StackHeight)(UIntPtr)memLoc)) {

                DebugPrint("<TryAll> set::rs: {0}/{1}::{2}->{3}\n",  
                           __arglist((uint)Magic.addressOf(obj),
                                     (uint)offset,
                                     (uint)(*(getLoc(obj,offset))),
                                     (uint)Magic.addressOf(data)));

                Magic.SetAt(obj, offset, data);
            }
        }

        internal static unsafe UIntPtr *enpointerize(UIntPtr inp) {
            return (UIntPtr *) inp;
        }
        internal static unsafe Object enpointerize2(UIntPtr inp) {
            return Magic.fromAddress(*(UIntPtr *) inp);
        }

        // aligns an address on the word boundary nearest it, after
        internal static UIntPtr alignStart(UIntPtr mem) {
            return mem & blockAlignmentNegMask;
        }
        // aligns an address on the word boundary nearest it, before
        internal static UIntPtr alignEnd(UIntPtr mem) {
            return (mem + (blockSize - 1)) & blockAlignmentNegMask;
        }

        // note that this should NOT be called for stuff on the stack lists (and
        // may give undefined results if such is done).  Eventually, these
        // functions should be invoked by the GC on the heap lists.  At the
        // moment, so as not to have to modify with the GC, it is done at Log
        // time.  The function has no effect on tryall support, it is solely to
        // keep the GC happy.

        internal struct FactoredPointer {
            internal Object baseObj;
            internal UIntPtr offset;
        }

        internal static int fixup = 0;
        internal static FactoredPointer fixupInterior(UIntPtr obj) {
            Object baseObj;
            UIntPtr offset;

            fixup++;

            VTable.Deny(isStack(obj), "fixup called on stack object");
            if(!isGcHeap(obj)) {
                baseObj = null;
                offset = obj;
            } else {
                UIntPtr addr = GC.installedGC.FindObjectAddr(obj);
                baseObj = Magic.fromAddress(addr);
                offset = obj - addr;
            }

            FactoredPointer result;
            result.baseObj = baseObj;
            result.offset = offset;
            return result;
        }

        // Information in this variable is essentially guaranteed garbage.  It is
        // just a nice fixed place in memory.
        private static UIntPtr staticDummyLogged = (UIntPtr) 0;

        private static UIntPtr blockSize {
            get {
                return (UIntPtr) UIntPtr.Size;
            }
        }

        private static UIntPtr blockAlignmentMask {
            get {
                return blockSize - 1;
            }
        }

        private static UIntPtr blockAlignmentNegMask {
            get {
                return ~blockAlignmentMask;
            }
        }

        //----------------------------------------------------------------------
        //
        // Fields

        internal TryAll[] savedTryAlls;
        internal int nextSavedTryAll;

        internal StackHeight currentTryAllStackHeight;
        internal TryAllStatus currentTryAllStatus;

        internal ReadEnlistmentLogWriter _rEnlistmentLogWriter;
        internal UpdateEnlistmentLogWriter _uEnlistmentLogWriter;
        internal UpdateLogWriter _updateLogWriter;

        internal ReadEnlistmentLog rEnlistmentLog;
        internal UpdateEnlistmentLog uEnlistmentLog;
        internal UpdateLog updateLog;
        internal UndoLog undoLog;

        internal TryAllCounters tryAllCounters;
        internal AtomicIsInvalidException atomicIsInvalidException;
        
        internal uint tokens;

        internal STMWord locallyAllocatedSTMWord;

        private static VisitMethod visitStrongRefsDelegate;
        private static VisitMethod visitWeakRefsDelegate;
        private static GCHookMethod preGCHookDelegate;
        private static GCHookMethod postGCHookDelegate;

        delegate void VisitMethod(DirectReferenceVisitor visitor);
        delegate void GCHookMethod();

        internal uint[] addressCache;
    }

    [NoLoggingForUndo]
    internal struct TryAll {
        internal StackHeight stackHeight;
        internal UpdateLog.Location updateLogAtStart;
        internal ReadEnlistmentLog.Location rEnlistmentLogAtStart;
        internal UpdateEnlistmentLog.Location uEnlistmentLogAtStart;
        internal UpdateEnlistmentLog.Entry[] locallyAllocatedEntry;
        internal STMWord locallyAllocatedSTMWord;
    }

    internal enum TryAllStatus {
        Active, ChosenCommit, Invalid
    }

    [NoLoggingForUndo]
    internal struct LogEntryUndoAction {
        // needed so we know when to invoke this action
        internal UpdateLog.Location updateLogAtRegistration;
        // the actual undo info
        internal IUndo UndoAction;
    }
    
    //----------------------------------------------------------------------
    //
    // Read enlistment log

    unsafe struct ReadEnlistmentLogWriter {
        internal ReadEnlistmentLog.Entry *next;
        internal ReadEnlistmentLog.Entry *limit;

        internal unsafe ReadEnlistmentLogWriter(ReadEnlistmentLog.Entry *next,
                                                ReadEnlistmentLog.Entry *limit) {
            this.next = next;
            this.limit = limit;
        }

        [Inline]
#if !DEBUG
        [DisableBoundsChecks]
        [DisableNullChecks]
#endif // !DEBUG
        internal static unsafe void EnsureLogMemory(TryAllManager m, uint bytesNeeded) {
            VTable.Assert(bytesNeeded <= TryAllManager.ENLISTMENT_LOG_CHUNK_SIZE * sizeof(ReadEnlistmentLog.Entry));
            TryAllManager.DebugPrint("ReadEnlistment: EnsureLogMemory : bytesNeeded={0} {1:x} {2:x}\n",
                                     __arglist(bytesNeeded,
                                               (UIntPtr)m._rEnlistmentLogWriter.next,
                                               (UIntPtr)m._rEnlistmentLogWriter.limit));

            if((UIntPtr) m._rEnlistmentLogWriter.next + bytesNeeded
                > (UIntPtr)m._rEnlistmentLogWriter.limit) {
                GetNewLogChunk(m);
             }             
        }

        [Inline]
#if !DEBUG
        [DisableBoundsChecks]
        [DisableNullChecks]
#endif // !DEBUG
        internal static unsafe void EnsureLogMemory(TryAllManager m) {
            TryAllManager.DebugPrint("ReadEnlistment: EnsureLogMemory {0:x} {1:x}\n",
                                     __arglist((UIntPtr)m._rEnlistmentLogWriter.next,
                                               (UIntPtr)m._rEnlistmentLogWriter.limit));

            if((UIntPtr) m._rEnlistmentLogWriter.next > 
               (UIntPtr)m._rEnlistmentLogWriter.limit) {
                GetNewLogChunk(m);
                VTable.Deny((UIntPtr) m._rEnlistmentLogWriter.next > 
                            (UIntPtr)m._rEnlistmentLogWriter.limit);
             }             
        }

        [NoInline]
        internal static void GetNewLogChunk(TryAllManager m) {
            //TryAllManager m = TryAllManager.CurrentRunningTryAll;
            ReadEnlistmentLog.SyncFromWriter(m);
            m._rEnlistmentLogWriter = ReadEnlistmentLog.GetInvalidWriter();
            m.rEnlistmentLog.AddCapacity(m);
            ReadEnlistmentLog.InitWriter(m);
            
            TryAllManager.DebugPrint("ReadEnlistmentLogWriter, entries[0]={0:x}\n", 
                                     __arglist(
                                     (UIntPtr)(m._rEnlistmentLogWriter.next)));

        }

#if !DEBUG
        [Inline] [DisableBoundsChecks] [DisableNullChecks]
#endif 
        internal static unsafe void Write(TryAllManager m, STMHandle h, bool ensure_after) {

            TryAllManager.DebugPrint("ReadEnlistment: Write {0:x} {1:x}\n",
                                     __arglist((UIntPtr)m._rEnlistmentLogWriter.next,
                                               (UIntPtr)m._rEnlistmentLogWriter.limit));

            VTable.Deny (m._rEnlistmentLogWriter.next > m._rEnlistmentLogWriter.limit);

            if (TryAllManager.DISABLE_BEFORE_FILTERING) {
                return;
            }

            if (TryAllManager.HASHING_FOR_READS) {
                uint[] cache = m.addressCache;
                VTable.Assert(cache != null);
                uint hash = (h.addr >> 2) & (uint) TryAllManager.HASH_MASK;
                
                uint key = ((uint)h.addr) ^ (uint)(m.tokens);
                TryAllManager.DebugPrint("Hashes to {0} mask={1}\n", 
                           __arglist(hash,
                                     TryAllManager.HASH_MASK));
                
                if (cache[hash] == (uint) key) {
                    TryAllManager.DebugPrint("Found\n");
                    m.tryAllCounters.IncrementReadsHitInCache();
                    return;
                } else {
                    TryAllManager.DebugPrint("Not found\n");
                    cache[hash] = (uint) key;
                }
                
            }

            if (TryAllManager.DISABLE_AFTER_FILTERING) {
                return;
            }

            STMSnapshot v = h.GetSTMSnapshot();
            if (TryAllManager.REMOVE_READ_AFTER_UPDATE_AT_ENLISTMENT) {
                STMWord w = v.GetSTMWord();
                if (w.IsOwned() && w.GetOwner() == m) {
                    TryAllManager.DebugPrint("EnlistForRead h=<{0:x}> v=<{1:x}> already enlisted for update by us\n", 
                                             __arglist(h.addr,
                                                       v.value));
                    m.tryAllCounters.IncrementUpdatesInReadEnlistmentsAtEnlistment();
                    return;
                }
            }

            //----------------------------------------------------------------------

            if (!TryAllManager.DISABLE_BEFORE_WRITING_LOG) {
                m.tryAllCounters.IncrementEnlistForReadLogged();
                
                ReadEnlistmentLog.Entry *ne = m._rEnlistmentLogWriter.next;
                ne -> h = h;
                ne -> v = v;
                ne++;
                m._rEnlistmentLogWriter.next = (ReadEnlistmentLog.Entry *) ne;
                
                TryAllManager.CountAsLogged();

                if (ensure_after) {
                    EnsureLogMemory(m); 
                }
            }

            TryAllManager.DebugPrint("EnlistForRead h=<{0:x}> v=<{1:x}> entry=<{2:x}>\n", 
                                     __arglist(h.addr,
                                               v.value,
                                               (UIntPtr)(m._rEnlistmentLogWriter.next)));

            //----------------------------------------------------------------------
        }
    }

    [NoLoggingForUndo]
    class ReadEnlistmentLog {
        internal ReadEnlistmentLog() {
            Entry[] entries = new Entry[TryAllManager.ENLISTMENT_LOG_CHUNK_SIZE];
            this.currentChunk = new LogChunk(entries, null);
        }
      
        // TODO: Inliner will not inline this method because of the pinned var
        // (and will warn repeatedly about it).
        //[Inline]
#if !DEBUG
        [DisableBoundsChecks]
        [DisableNullChecks]
#endif // !DEBUG
        internal unsafe Entry *AddrOfEntry(int idx) {
            Entry[] entries = this.currentChunk.entries;
            UIntPtr addrAsUIntPtr;
            Entry *result;

            fixed (Entry *baseAddr = &entries[0]) {
                Entry *entryAddr = baseAddr + idx;
                addrAsUIntPtr = (UIntPtr) entryAddr;
            }

            result = (Entry *) addrAsUIntPtr;

            return result;
        }

        // TODO: Inliner will not inline this method because of the pinned var
        // (and will warn repeatedly about it).
        //[Inline]
#if !DEBUG
        [DisableBoundsChecks]
        [DisableNullChecks]
#endif // !DEBUG
        internal unsafe uint AddrToIndex(Entry *entryPtr) {
            uint result;
            UIntPtr baseAddr;
            fixed (Entry *basePtr = &this.currentChunk.entries[0]) {
                baseAddr = (UIntPtr)basePtr;
            }
            UIntPtr entryAddr = (UIntPtr)entryPtr;
            result = (uint)((int)(entryAddr - baseAddr)) / ((uint)sizeof (Entry));
            return (uint)result;
        }

        internal bool NotEmpty() {
            return ((this.currentChunk.nextEntry != 0) || (this.currentChunk.next != null));
        }

        // For each enlistment was log the STMSnapshot we saw when we enlisted
        // the object.  The STM guarantees that the STM snapshot changes
        // every time the object is opened for update: we'll detect conflicts
        // because we'll see a different STMSnapshot at validation.

        internal struct Entry {
            internal STMHandle h;
            internal STMSnapshot v;
        }

        internal class LogChunk {
            internal LogChunk(Entry[] entries,LogChunk next) {
                this.entries = entries;
                this.next = next;
            }
        
            internal Entry[] entries;
            internal LogChunk next;
            internal int nextEntry;
        }
    

        internal unsafe void Dump() {
            VTable.DebugPrint("ReadEnlistment log:\n");
            LogChunk chunk = this.currentChunk;
            int lowIdx = 0;
            int highIdx = chunk.nextEntry;

            while (chunk != null) {
                Entry[] entries = chunk.entries;
                VTable.DebugPrint("chunk={0} entries={1}\n",
                                  __arglist((uint)(Magic.addressOf(chunk)),
                                            (uint)(Magic.addressOf(entries))));

                for (int i = lowIdx; i < highIdx; i++) {
                    VTable.DebugPrint("entry[{0}] : <{1}> logged: <{2}> now: <{3}>\n",
                                      __arglist(i,
                                                (uint)(entries[i].h.addr),
                                                (uint)(entries[i].v.value),
                                                (uint)(entries[i].h.GetSTMSnapshot().GetSTMWord().value)));

                }

                chunk = chunk.next;
                highIdx = TryAllManager.ENLISTMENT_LOG_CHUNK_SIZE;
            }
        }

        [NoInline]
        internal void AddCapacity(TryAllManager m) {
            m.tryAllCounters.IncrementEnlistmentOverflow();

            // NB: construct these objects before linking them in case
            // the write barriers cause GC.

            Entry[] newEntries = 
                new Entry[TryAllManager.ENLISTMENT_LOG_CHUNK_SIZE];

            LogChunk newNode = 
                new LogChunk(newEntries, this.currentChunk);

            // NB: Storing to currentChunk may trip the write barrier.
            // We need to make sure that the visitation code will work
            // at any of those points.  This means we write to currentChunk
            // first: if that causes a GC then we can scan the previous
            // chunk without having corrupted nextEntry.

            this.currentChunk = newNode;
        }
    
        [InlineCopyAttribute]
        internal struct Location {
            internal Location(LogChunk node, int entry) {
                this.node = node;
                this.entry = entry;
            }
        
            internal static bool Eq(Location l1, Location l2) {
                return (l1.entry == l2.entry) && (l1.node == l2.node);
            }

            internal static int ToDebugIdx(Location l1) {
                LogChunk n1 = l1.node;
                int result = 0;

                while (n1.next != null) {
                    result += TryAllManager.ENLISTMENT_LOG_CHUNK_SIZE;
                    n1 = n1.next;
                }
                result += l1.entry;
                return result;
            }

            internal LogChunk node;
            internal int entry;
        }

        internal Location CurrentLocation {
            get {
                return new Location(this.currentChunk, this.currentChunk.nextEntry);
            }
        }

        internal int Size {
            get {
                int size = 0;
                for(LogChunk node = this.currentChunk;
                    node != null;
                    node = node.next) {
                    size += node.entries.Length;
                }
                return size;
            }
        }

#if !DEBUG
        [DisableBoundsChecks]
        [DisableNullChecks]
#endif // !DEBUG
        internal static unsafe void SyncFromWriter(TryAllManager m) {
            ReadEnlistmentLog l = m.rEnlistmentLog;

            if (m._rEnlistmentLogWriter.next != null) {
                l.currentChunk.nextEntry = (int)l.AddrToIndex(m._rEnlistmentLogWriter.next);
            }

            VTable.Assert(l.currentChunk.nextEntry >= 0);
            VTable.Assert(l.currentChunk.nextEntry <= TryAllManager.ENLISTMENT_LOG_CHUNK_SIZE);

            TryAllManager.DebugPrint("ReadEnlistmentLogWriter : sync when nextEntry={0}\n",
                                     __arglist(l.currentChunk.nextEntry));
        }

        internal static unsafe ReadEnlistmentLogWriter GetInvalidWriter() {
            return new ReadEnlistmentLogWriter(null, null);
        }

#if !DEBUG
        [DisableBoundsChecks]
        [DisableNullChecks]
#endif // !DEBUG
        internal static unsafe bool WriterIsValid(ReadEnlistmentLogWriter w) {
            return (w.next != null);
        }

#if !DEBUG
        [DisableBoundsChecks]
        [DisableNullChecks]
#endif // !DEBUG
        internal static unsafe void InitWriter(TryAllManager m) {
            ReadEnlistmentLog r = m.rEnlistmentLog;
            Entry *next = r.AddrOfEntry(r.currentChunk.nextEntry);
            Entry *limit = r.AddrOfEntry(TryAllManager.ENLISTMENT_LOG_CHUNK_SIZE - 1);
            
            TryAllManager.DebugPrint("ReadEnlistmentLogWriter : nextEntry={0} next={1} limit={2}\n",
                                     __arglist(r.currentChunk.nextEntry,
                                               (uint)(UIntPtr)next,
                                               (uint)(UIntPtr)limit));

            m._rEnlistmentLogWriter.next = next;
            m._rEnlistmentLogWriter.limit = limit;
        }

#if !DEBUG
        [Inline] [DisableBoundsChecks] [DisableNullChecks]
#endif 
        internal unsafe void Validate(TryAllManager m, bool duringGC) {
            LogChunk chunk = this.currentChunk;
            Entry[] entries = chunk.entries;
            int endEntry = chunk.nextEntry;
            int oldestEntry = m.savedTryAlls[0].rEnlistmentLogAtStart.entry;

            TryAllManager.DebugPrint("Pre-validation status {0} {1}\n",
                                     __arglist((int)m.currentTryAllStatus,
                                               duringGC ? "(during GC)" : "(not during GC)"));

            m.Shake(duringGC);

            do {
                int startEntry = (chunk.next == null) ? oldestEntry : 0;
                
                VTable.Assert((chunk != m.savedTryAlls[0].rEnlistmentLogAtStart.node) || 
                              (chunk.next == null));

                for (int entry = startEntry; entry < endEntry; entry++) {
                    STMHandle h = entries[entry].h;

                    STMSnapshot oldSnapshot = entries[entry].v;
                    STMSnapshot curSnapshot = h.GetSTMSnapshot();
                    
                    TryAllManager.DebugPrint("index {0} h=<{1:x}> logged=<{2:x}> now=<{3:x}>\n", 
                                             __arglist(entry,
                                                       h.addr,
                                                       oldSnapshot.value,
                                                       curSnapshot.value));

                    if (oldSnapshot.value == curSnapshot.value) {
                        if (curSnapshot.ZeroIfMustBeQuiescent() == 0) {
                            // Fast test succeeded: certainly quiescent
                        } else {
                            STMWord curWord = curSnapshot.GetSTMWord();
                            if (curWord.IsQuiescent()) {
                                // Unchanged, not enlisted by anyone
                            } else if (curWord.GetOwner() == m) {
                                // Previously enlisted by us
                                VTable.Assert(m.uEnlistmentLog.NotEmpty());
                            } else {
                                // Previously enlisted by someone else 
                                m.tryAllCounters.IncrementInvalidConflict();
                                m.becomeInvalid(duringGC);
                            }
                        }
                    } else {
                        STMWord curWord = curSnapshot.GetSTMWord();
                        if (curWord.IsQuiescent()) {
                            if (curWord.Eq(oldSnapshot.GetSTMWord())) {
                                // Inflated, but no conflicting STM operation
                                m.tryAllCounters.IncrementInflationSeen();
                            } else {
                                // Updated by someone else after we enlisted it
                                m.tryAllCounters.IncrementInvalidConflict();
                                m.becomeInvalid(duringGC);
                            }
                        } else if (curWord.GetOwner() == m) {
                            // Subsequently enlisted by us...
                            VTable.Assert(m.uEnlistmentLog.NotEmpty());
                            if (curWord.GetOwnersVersion().Eq(oldSnapshot)) {
                                // ...without intervening update
                            } else {
                                // ...but updated by someone else before then
                                m.tryAllCounters.IncrementInvalidConflict();
                                m.becomeInvalid(duringGC);
                            }
                        } else {
                            // Subsequently enlisted by someone else
                            m.tryAllCounters.IncrementInvalidConflict();
                            m.becomeInvalid(duringGC);
                        }
                    }
                }
                
                if (chunk.next == null) break;
                chunk = chunk.next;
                entries = chunk.entries;
                endEntry = chunk.nextEntry;
            } while (true);

            TryAllManager.DebugPrint("{0:x}: Post-validation status {1}\n",
                                     __arglist(Magic.addressOf(m),
                                               (int)m.currentTryAllStatus));
        }

#if !DEBUG
        [Inline] [DisableBoundsChecks] [DisableNullChecks]
#endif 
        internal void DismissFrom(TryAllManager m, Location l) {
            TryAllManager.DebugPrint("Dismissing read enlistments from {0} to {1}\n",
                                     __arglist(Location.ToDebugIdx(l),
                                               Location.ToDebugIdx(CurrentLocation)));


            this.currentChunk = l.node;
            this.currentChunk.nextEntry = l.entry;
        }

#if !DEBUG
        [DisableBoundsChecks]
        [DisableNullChecks]
#endif // !DEBUG
        internal unsafe void VisitWeakRefs(TryAllManager m, 
                                           DirectReferenceVisitor rv) {
            LogChunk fromChunk = this.currentChunk;
            Entry[] fromEntries = fromChunk.entries;
            int fromEntry = fromChunk.nextEntry;
            int fromNumBlocks = 1;

            LogChunk toChunk = fromChunk;
            Entry[] toEntries = fromEntries;
            int toEntry = fromEntry;
            int toNumBlocks = 1;

            for (int depth = m.nextSavedTryAll - 1; depth >= 0; depth --) {
                LogChunk endFromChunk = m.savedTryAlls[depth].rEnlistmentLogAtStart.node;
                int endFromEntry = m.savedTryAlls[depth].rEnlistmentLogAtStart.entry;

                endFromChunk = TryAllManager.toReadEnlistmentLogChunk(TryAllManager.ReadBarrier(rv, 
                                                                                                endFromChunk));
                
                TryAllManager.DebugPrintGC("Visiting read enlistments for {0:x} depth {1} ({2:x}:{3})\n", 
                                    __arglist((UIntPtr)Magic.addressOf(m),
                                              depth,
                                              Magic.addressOf(endFromChunk),
                                              endFromEntry));
                
                while (true) {
                    bool inEndChunk = (fromChunk == endFromChunk);
                    int downTo = inEndChunk ? endFromEntry : 0;
                    
                    for (fromEntry --; fromEntry >= downTo; fromEntry --) {
                        STMHandle h = fromEntries[fromEntry].h;
                        STMWord curWord = h.GetSTMSnapshot().GetSTMWord();

                        TryAllManager.DebugPrintGC("saw index {0:x}/{1} {2:x} {3:x} in read enlistments\n",
                                            __arglist(Magic.addressOf(fromEntries),
                                                      fromEntry,
                                                      h.addr,
                                                      curWord.value));
                        
                        // Check if the referent has died

                        bool keep;
                        if ((h.addr != UIntPtr.Zero) &&
                            (!fromEntries[fromEntry].h.Visit(rv))) {
                            keep = false;
                            TryAllManager.DebugPrintGC("   cleared weak ref\n");
                            m.tryAllCounters.IncrementWeakRefsClearedInReadEnlistmentLog();
                        } else {
                            keep = true;
                        }

                        if (keep) {
                            // Move on to the next to-chunk if we've filled one
                            if (toEntry == 0) {
                                toChunk = toChunk.next;
                                toEntries = toChunk.entries;
                                toEntry = toEntries.Length;
                                
                                toChunk.nextEntry = toEntries.Length;
                                toNumBlocks ++;
                            }
                            
                            // Claim a slot in toEntries
                            toEntry --;
                            
                            // Copy the entry to the to-chunk, visit the
                            // pointer-derived values in it
                            toEntries[toEntry] = fromEntries[fromEntry];
                            toEntries[toEntry].v.Visit(rv);
                            
                            TryAllManager.DebugPrintGC("   --> {0:x}/{1} {2:x} {3:x}\n",
                                                __arglist(Magic.addressOf(toEntries),
                                                          toEntry,
                                                          toEntries[toEntry].h.addr,
                                                          toEntries[toEntry].v.value));
                        }
                    }
                    
                    if (inEndChunk) {
                        break;
                    }
                    
                    // Move on to the next from-chunk
                    fromChunk = fromChunk.next;
                    fromEntries = fromChunk.entries;
                    fromEntry = fromChunk.nextEntry;
                    fromNumBlocks ++;
                }
                
                // Update finishing point
                TryAllManager.DebugPrintGC("Log now starts at {0:x}:{1}\n",
                                           __arglist(Magic.addressOf(toChunk),
                                                     toEntry));
                m.savedTryAlls[depth].rEnlistmentLogAtStart.node = toChunk;
                m.savedTryAlls[depth].rEnlistmentLogAtStart.entry = toEntry;

            }
            
            VTable.Assert(fromChunk.next == null);
            toChunk.next = null;

            if (TryAllManager.ENABLE_PROFILING) {
                if (VTable.enableGCTiming) {
                    VTable.DebugPrint("[Read enlistment log: {0}->{1} * {2}]\n",
                                      __arglist(fromNumBlocks,
                                                toNumBlocks,
                                                TryAllManager.ENLISTMENT_LOG_CHUNK_SIZE));
                }
            }

#if DEBUG
            for (int i = 0; i < toEntry; i ++) {
                toEntries[i].h.addr = (UIntPtr)TryAllManager.DEAD_PTR;
                toEntries[i].v.value = UIntPtr.Zero;
            }
#endif
        }

#if !DEBUG
        [DisableBoundsChecks]
        [DisableNullChecks]
#endif // !DEBUG
        internal unsafe void ValidateAndRemoveDuplicates(TryAllManager m) {
            LogChunk fromChunk = this.currentChunk;
            Entry[] fromEntries = fromChunk.entries;
            int fromEntry = fromChunk.nextEntry;
            int fromNumBlocks = 1;

            LogChunk toChunk = fromChunk;
            Entry[] toEntries = fromEntries;
            int toEntry = fromEntry;
            int toNumBlocks = 1;

            for (int depth = m.nextSavedTryAll - 1; depth >= 0; depth --) {
                LogChunk startToChunk = toChunk;
                int startToEntry = toEntry;
                
                LogChunk endFromChunk = m.savedTryAlls[depth].rEnlistmentLogAtStart.node;
                int endFromEntry = m.savedTryAlls[depth].rEnlistmentLogAtStart.entry;

                TryAllManager.DebugPrintGC("Visiting read enlistments for {0:x} depth {1} ({2:x}:{3})\n", 
                                    __arglist((UIntPtr)Magic.addressOf(m),
                                              depth,
                                              Magic.addressOf(endFromChunk),
                                              endFromEntry));
                
                while (true) {
                    bool inEndChunk = (fromChunk == endFromChunk);
                    int downTo = inEndChunk ? endFromEntry : 0;
                    

                    for (fromEntry --; fromEntry >= downTo; fromEntry --) {
                        STMHandle h = fromEntries[fromEntry].h;
                        STMWord curWord = h.GetSTMSnapshot().GetSTMWord();

                        TryAllManager.DebugPrintGC("saw index {0:x}/{1} {2:x} {3:x} in read enlistments chunk {4:x}\n",
                                            __arglist(Magic.addressOf(fromEntries),
                                                      fromEntry,
                                                      h.addr,
                                                      curWord.value,
                                                      Magic.addressOf(fromChunk)));
                        
                        bool keep = false;

                        STMSnapshot oldSnapshot = fromEntries[fromEntry].v;
                        STMSnapshot curSnapshot = h.GetSTMSnapshot();
                        
                        TryAllManager.DebugPrintGC("index {0} h=<{1:x}> logged=<{2:x}> now=<{3:x}>\n", 
                                                   __arglist(fromEntry,
                                                             h.addr,
                                                             oldSnapshot.value,
                                                             curSnapshot.value));
                        
                        keep = true;
                        if (TryAllManager.REMOVE_READ_DUPLICATES_AT_GC && keep) {
                            if (fromEntries[fromEntry].h.IsMarked()) {
                                TryAllManager.DebugPrintGC("   is duplicate\n");
                                keep = false;
                                m.tryAllCounters.IncrementReadDuplicatesRemoved();
                            } 
                        }
                        
                        
                        if (keep) {
                            if (oldSnapshot.Eq(curSnapshot)) {
                                if (curWord.IsQuiescent()) {
                                    // Unchanged, not enlisted by anyone
                                } else if (curWord.GetOwner() == m) {
                                    // Previously enlisted by us
                                    m.tryAllCounters.IncrementUpdatesInReadEnlistmentsAtGC();
                                    keep = false;
                                        VTable.Assert(m.uEnlistmentLog.NotEmpty());
                                } else {
                                    // Previously enlisted by someone else 
                                    m.tryAllCounters.IncrementInvalidConflict();
                                    m.becomeInvalid(true);
                                        keep = false;
                                }
                            } else {
                                if (curWord.IsQuiescent()) {
                                    if (curWord.Eq(oldSnapshot.GetSTMWord())) {
                                        // Inflated, but no conflicting STM operation
                                        m.tryAllCounters.IncrementInflationSeen();
                                    } else {
                                        // Updated by someone else after we enlisted it
                                        m.tryAllCounters.IncrementInvalidConflict();
                                        m.becomeInvalid(true);
                                        keep = false;
                                    }
                                } else if (curWord.GetOwner() == m) {
                                    // Subsequently enlisted by us...
                                    VTable.Assert(m.uEnlistmentLog.NotEmpty());
                                    if (curWord.GetOwnersVersion().Eq(oldSnapshot)) {
                                        // ...without intervening update
                                        m.tryAllCounters.IncrementUpdatesInReadEnlistmentsAtGC();
                                        keep = false;
                                    } else {
                                        // ...but updated by someone else before then
                                        m.tryAllCounters.IncrementInvalidConflict();
                                        m.becomeInvalid(true);
                                        keep = false;
                                    }
                                } else {
                                    // Subsequently enlisted by someone else
                                    m.tryAllCounters.IncrementInvalidConflict();
                                    m.becomeInvalid(true);
                                    keep = false;
                                }
                            }
                        }
                        
                        if (TryAllManager.REMOVE_READ_DUPLICATES_AT_GC && keep) {
                            TryAllManager.DebugPrintGC("   setting mark\n");
                            fromEntries[fromEntry].h.SetMark(true);
                        }

                        if (keep) {
                            // Move on to the next to-chunk if we've filled one
                            if (toEntry == 0) {
                                toChunk = toChunk.next;
                                toEntries = toChunk.entries;
                                toEntry = toEntries.Length;
                                
                                toChunk.nextEntry = toEntries.Length;
                                toNumBlocks ++;
                            }
                            
                            // Claim a slot in toEntries
                            toEntry --;
                            
                            // Copy the entry to the to-chunk, visit the
                            // pointer-derived values in it
                            toEntries[toEntry] = fromEntries[fromEntry];
                            
                            TryAllManager.DebugPrintGC("   --> {0:x}/{1} {2:x}\n",
                                                __arglist(Magic.addressOf(toEntries),
                                                          toEntry,
                                                          toEntries[toEntry].h.addr));
                        } 
                    }
                    
                    if (inEndChunk) {
                        break;
                    }
                    
                    // Move on to the next from-chunk
                    fromChunk = fromChunk.next;
                    fromEntries = fromChunk.entries;
                    fromEntry = fromChunk.nextEntry;
                    fromNumBlocks ++;
                }
                
                // Update finishing point
                TryAllManager.DebugPrintGC("Log now starts at {0:x}:{1}\n",
                                           __arglist(Magic.addressOf(toChunk),
                                                     toEntry));
                m.savedTryAlls[depth].rEnlistmentLogAtStart.node = toChunk;
                m.savedTryAlls[depth].rEnlistmentLogAtStart.entry = toEntry;

                // Clear marks on retained objects (if removing duplicates)
                if (TryAllManager.REMOVE_READ_DUPLICATES_AT_GC) {
                    LogChunk tempChunk = startToChunk;
                    Entry[] tempEntries = startToChunk.entries;
                    int tempEntry = startToEntry;

                    while (true) {
                        bool inEndChunk = (tempChunk == toChunk);
                        int downTo = inEndChunk ? toEntry : 0;
                        
                        for (tempEntry --; tempEntry >= downTo; tempEntry --) {
                            STMHandle h = tempEntries[tempEntry].h;
                            TryAllManager.DebugPrintGC("clearing mark on {0:x}/{1} {2} in read enlistments\n",
                                                __arglist(Magic.addressOf(tempChunk),
                                                          tempEntry,
                                                          h.addr));

                            VTable.Assert(tempEntries[tempEntry].h.IsMarked());
                            tempEntries[tempEntry].h.SetMark(false);
                        }

                        if (inEndChunk) {
                            break;
                        }
                        
                        // Move on to the next temp-chunk
                        tempChunk = tempChunk.next;
                        tempEntries = tempChunk.entries;
                        tempEntry = tempChunk.nextEntry;
                    }
                }
            }
            
            VTable.Assert(fromChunk.next == null);
            toChunk.next = null;

            if (TryAllManager.ENABLE_PROFILING) {
                if (VTable.enableGCTiming) {
                    VTable.DebugPrint("[Read enlistment log: {0}->{1} * {2}]\n",
                                      __arglist(fromNumBlocks,
                                                toNumBlocks,
                                                TryAllManager.ENLISTMENT_LOG_CHUNK_SIZE));
                }
            }

#if DEBUG
            for (int i = 0; i < toEntry; i ++) {
                toEntries[i].h.addr = (UIntPtr)TryAllManager.DEAD_PTR;
                toEntries[i].v.value = UIntPtr.Zero;
            }
#endif
        }

        internal LogChunk currentChunk;
    }

    //----------------------------------------------------------------------
    //
    // Update enlistment log

    unsafe struct UpdateEnlistmentLogWriter {
        internal UpdateEnlistmentLog.Entry *next;
        internal UpdateEnlistmentLog.Entry *limit;

        internal unsafe UpdateEnlistmentLogWriter(UpdateEnlistmentLog.Entry *next,
                                                  UpdateEnlistmentLog.Entry *limit) {
            this.next = next;
            this.limit = limit;
        }

        [Inline]
#if !DEBUG
        [DisableBoundsChecks]
        [DisableNullChecks]
#endif // !DEBUG
        internal static void EnsureLogMemory(TryAllManager m, uint bytesNeeded) {
            VTable.Assert(bytesNeeded <= TryAllManager.ENLISTMENT_LOG_CHUNK_SIZE * sizeof(UpdateEnlistmentLog.Entry));
            TryAllManager.DebugPrint("UpdateEnlistment: EnsureLogMemory : bytesNeeded={0} {1:x} {2:x}\n",
                                     __arglist(bytesNeeded,
                                               (UIntPtr)m._uEnlistmentLogWriter.next,
                                               (UIntPtr)m._uEnlistmentLogWriter.limit));

            if((UIntPtr) m._uEnlistmentLogWriter.next + bytesNeeded
                > (UIntPtr)m._uEnlistmentLogWriter.limit) {
                 GetNewLogChunk(m);
             }             
        }

        [Inline]
#if !DEBUG
        [DisableBoundsChecks]
        [DisableNullChecks]
#endif // !DEBUG
        internal static void EnsureLogMemory(TryAllManager m) {
            TryAllManager.DebugPrint("UpdateEnlistment: EnsureLogMemory {0:x} {1:x}\n",
                                     __arglist((UIntPtr)m._uEnlistmentLogWriter.next,
                                               (UIntPtr)m._uEnlistmentLogWriter.limit));

            if((UIntPtr) m._uEnlistmentLogWriter.next >
               (UIntPtr)m._uEnlistmentLogWriter.limit) {
                 GetNewLogChunk(m);
             }             
        }

        [NoInline]
        internal static unsafe void GetNewLogChunk(TryAllManager m) {
            // TryAllManager m = TryAllManager.CurrentRunningTryAll;
            UpdateEnlistmentLog.SyncFromWriter(m);
            m._uEnlistmentLogWriter = UpdateEnlistmentLog.GetInvalidWriter();
            m.uEnlistmentLog.AddCapacity(m);
            UpdateEnlistmentLog.InitWriter(m);
            
            TryAllManager.DebugPrint("UpdateEnlistmentLogWriter, entries[0]={0}\n",
                                     __arglist((UIntPtr)(m._uEnlistmentLogWriter.next)));
        }

#if !DEBUG
        [Inline] [DisableBoundsChecks] [DisableNullChecks]
#endif 
        internal static unsafe void Write(TryAllManager m, STMHandle h, bool ensureAfter) {
            
            if (TryAllManager.DISABLE_BEFORE_FILTERING ||
                TryAllManager.DISABLE_AFTER_FILTERING) {
                return;
            }

            TryAllManager.DebugPrint("UpdateEnlistment: Write h={0:x} {1:x} {2:x}\n",
                                     __arglist(h.addr,
                                               (UIntPtr)m._uEnlistmentLogWriter.next,
                                               (UIntPtr)m._uEnlistmentLogWriter.limit));

            VTable.Deny(m._uEnlistmentLogWriter.next > m._uEnlistmentLogWriter.limit);

            STMSnapshot curSnap = h.GetSTMSnapshot();
            STMWord curWord = curSnap.GetSTMWord();
            TryAllManager.DebugPrint("EnlistForUpdate h=<{0:x}> v=<{1:x}> entry=<{2:x}>\n",
                                     __arglist(h.addr,
                                               curWord.value,
                                               (UIntPtr)(m._uEnlistmentLogWriter.next)));

            if (curWord.IsQuiescent()) {
                // Nobody seems to have enlisted it yet.  NB: we must write
                // the log entry first and only then attempt to claim ownership.
                // This is because claiming ownership may trigger a GC if it
                // causes a multi-use-word to be inflated.  The GC will need
                // to scan the new log entry so that it can update the
                // reference-derived values in it.

                if (!TryAllManager.DISABLE_BEFORE_WRITING_LOG) {
                    UpdateEnlistmentLog.Entry *ne = m._uEnlistmentLogWriter.next;
                    ne -> h = h;
                    ne -> v = curWord;
                    STMWord newWord = new STMWord((UIntPtr)ne, true);
                    ne ++;
                    m._uEnlistmentLogWriter.next = (UpdateEnlistmentLog.Entry *)ne;
                    
                    bool success = h.CompareExchangeSTMWord(newWord.value,
                                                            curWord.value, 
                                                            curSnap);
                    
                    if (!success) {
                        ne --;
                        m._uEnlistmentLogWriter.next = (UpdateEnlistmentLog.Entry *)ne;
                        
                        TryAllManager.DebugPrint("Race during enlistment\n");
                        
                        m.tryAllCounters.IncrementInvalidRace();
                        m.becomeInvalid(false); // Not during GC
                    } else {
                        
                        TryAllManager.CountAsLogged();
                        m.tryAllCounters.IncrementEnlistForUpdateLogged();
                        if (ensureAfter) {
                            EnsureLogMemory(m);
                        }
                    }
                }
            } else if (curWord.GetOwner() == m) {
                // We have already enlisted it for update

                TryAllManager.DebugPrint("Already enlisted for update by us\n");
            } else {
                // Someone else has enlisted it for update
                TryAllManager.DebugPrint("Already enlisted for another tm\n");
                m.tryAllCounters.IncrementInvalidConflict();
                m.becomeInvalid(false); // Not during GC
            } 
        }

#if !DEBUG
        [Inline] [DisableBoundsChecks] [DisableNullChecks]
#endif 
        internal static unsafe void WriteNew(TryAllManager m, STMHandle h, bool ensureAfter) {

            if (TryAllManager.DISABLE_BEFORE_FILTERING ||
                TryAllManager.DISABLE_AFTER_FILTERING) {
                return;
            }

            TryAllManager.DebugPrint("UpdateEnlistment: Write {0:x} {1:x}\n",
                                     __arglist((UIntPtr)m._uEnlistmentLogWriter.next,
                                               (UIntPtr)m._uEnlistmentLogWriter.limit));

            VTable.Deny(m._uEnlistmentLogWriter.next > m._uEnlistmentLogWriter.limit);
            TryAllManager.DebugPrint("EnlistNewObjForUpdate h=<{0:x}> snapshot=<{1:x}>\n",
                                     __arglist(h.addr,
                                               h.GetSTMSnapshot().value));
            VTable.Assert(h.GetSTMSnapshot().value == UIntPtr.Zero);

            TryAllManager.DebugPrint("EnlistNewObjForUpdate h=<{0:x}> entry=<{1:x}> word {2:x}\n",
                                     __arglist(h.addr,
                                               (UIntPtr)(m._uEnlistmentLogWriter.next),
                                               m.locallyAllocatedSTMWord.value));
            
            if (!TryAllManager.DISABLE_BEFORE_WRITING_LOG) {
                UpdateEnlistmentLog.Entry *ne = m._uEnlistmentLogWriter.next;
                ne -> h = h;
                ne -> v.value = UIntPtr.Zero;
                TryAllManager.DebugPrint("EnlistNewObjForUpdate m=<{0:x}> {1:x} offset={2:x} {3:x}\n",
                                         __arglist((UIntPtr)(ne -> m),
                                                   Magic.addressOf(m),
                                                   (UIntPtr)(ne -> offset),
                                                   ((UIntPtr)ne) - Magic.addressOf(m.uEnlistmentLog.currentChunk.entries)));
                VTable.Assert(ne -> m == Magic.addressOf(m));
                VTable.Assert(ne -> offset == ((UIntPtr)ne) - Magic.addressOf(m.uEnlistmentLog.currentChunk.entries));
                
                ne ++;
                m._uEnlistmentLogWriter.next = (UpdateEnlistmentLog.Entry *)ne;

                h.SetSTMWordAtAllocation(m.locallyAllocatedSTMWord);

                TryAllManager.CountAsLogged();
                m.tryAllCounters.IncrementEnlistForUpdateLogged();

                if (ensureAfter) {
                    EnsureLogMemory(m);
                }
            }
        }
    }

    [NoLoggingForUndo]
    class UpdateEnlistmentLog {

        internal UpdateEnlistmentLog(TryAllManager m) {
            AddCapacity(m);
        }
      
        // TODO: Inliner will not inline this method because of the pinned var
        // (and will warn repeatedly about it).
        //[Inline]
        internal static unsafe Entry *AddrOfEntry(Entry[] entries, int idx) {
            UIntPtr addrAsUIntPtr;
            Entry *result;

            fixed (Entry *baseAddr = &entries[0]) {
                Entry *entryAddr = baseAddr + idx;
                addrAsUIntPtr = (UIntPtr) entryAddr;
            }

            result = (Entry *) addrAsUIntPtr;

            return result;
        }

        // TODO: Inliner will not inline this method because of the pinned var
        // (and will warn repeatedly about it).
        //[Inline]
#if !DEBUG
        [DisableBoundsChecks]
        [DisableNullChecks]
#endif // !DEBUG
        internal unsafe uint AddrToIndex(Entry *entryPtr) {
            uint result;
            UIntPtr baseAddr;
            fixed (Entry *basePtr = &this.currentChunk.entries[0]) {
                baseAddr = (UIntPtr)basePtr;
            }
            UIntPtr entryAddr = (UIntPtr)entryPtr;
            result = (uint)((int)(entryAddr - baseAddr)) / ((uint)sizeof (Entry));
            return (uint)result;
        }

        internal bool NotEmpty() {
            return ((this.currentChunk.nextEntry != 0) || (this.currentChunk.next != null));
        }

#if !DEBUG
        [DisableBoundsChecks]
        [DisableNullChecks]
#endif // !DEBUG
        internal unsafe Entry *AddrOfEntry(int idx) {
            Entry[] entries = this.currentChunk.entries;
            Entry *result = AddrOfEntry(entries, idx);
            return result;
        }

#if !DEBUG
        [DisableBoundsChecks]
        [DisableNullChecks]
#endif // !DEBUG
        internal static unsafe void SyncFromWriter(TryAllManager m) {
            UpdateEnlistmentLog u = m.uEnlistmentLog;

            if (m._uEnlistmentLogWriter.next != null) {
                u.currentChunk.nextEntry = (int)u.AddrToIndex(m._uEnlistmentLogWriter.next);
            }

            VTable.Assert(u.currentChunk.nextEntry >= 0);
            VTable.Assert(u.currentChunk.nextEntry <= TryAllManager.ENLISTMENT_LOG_CHUNK_SIZE);

            TryAllManager.DebugPrint("UpdateEnlistmentLogWriter : sync when nextEntry={0}\n",
                                     __arglist(u.currentChunk.nextEntry));
        }

        internal static unsafe UpdateEnlistmentLogWriter GetInvalidWriter() {
            return new UpdateEnlistmentLogWriter(null, null);
        }

#if !DEBUG
        [DisableBoundsChecks]
        [DisableNullChecks]
#endif // !DEBUG
        internal static unsafe bool WriterIsValid(UpdateEnlistmentLogWriter w) {
            return (w.next != null);
        }

#if !DEBUG
        [DisableBoundsChecks]
        [DisableNullChecks]
#endif // !DEBUG
        internal static unsafe void InitWriter(TryAllManager m) {
            UpdateEnlistmentLog u = m.uEnlistmentLog;
            Entry *next = u.AddrOfEntry(u.currentChunk.nextEntry);
            Entry *limit = u.AddrOfEntry(TryAllManager.ENLISTMENT_LOG_CHUNK_SIZE - 1);
            
            TryAllManager.DebugPrint("UpdateEnlistmentLogWriter : nextEntry={0} next={1} limit={2}\n",
                                     __arglist(u.currentChunk.nextEntry,
                                               (uint)(UIntPtr)next,
                                               (uint)(UIntPtr)limit));

            m._uEnlistmentLogWriter.next = next;
            m._uEnlistmentLogWriter.limit = limit;
        }

#if !DEBUG
        [Inline] [DisableBoundsChecks] [DisableNullChecks]
#endif 
        private unsafe void DismissChunkBetween(TryAllManager m, 
                                                LogChunk chunk, 
                                                int lowIdx,
                                                int highIdx) 
        {
            TryAllManager.DebugPrint("Dismissing chunk {0:x} {1}..{2} (Length={3})\n",
                                     __arglist(Magic.addressOf(chunk),
                                               lowIdx,
                                               highIdx,
                                               chunk.nextEntry));

            VTable.Assert(lowIdx >= 0);
            VTable.Assert(lowIdx <= highIdx);
            VTable.Assert(highIdx <= chunk.nextEntry);

            Entry[] entries = chunk.entries;
            for (int entry = lowIdx; entry < highIdx; entry++) {
                STMHandle h = entries[entry].h;
                
                TryAllManager.DebugPrint("index {0} h=<{1:x}> m={2:x} {3:x}\n", 
                                         __arglist(entry,
                                                   h.addr,
                                                   entries[entry].m,
                                                   Magic.addressOf(m)));
                TryAllManager.DebugPrint("Version at enlistment {0:x}\n",
                                         __arglist(entries[entry].v.value));
                VTable.Assert(entries[entry].m == Magic.addressOf(m));
                h.RefreshSTMWord(entries[entry].v.GetNextVersion());
            }
            TryAllManager.DebugPrint("Dismissed chunk {0:x} entries {1:x} {2}..{3}\n",
                                     __arglist(Magic.addressOf(chunk),
                                               Magic.addressOf(entries),
                                               lowIdx,
                                               highIdx));;
        }

#if !DEBUG
        [Inline] [DisableBoundsChecks] [DisableNullChecks]
#endif 
        internal void DismissFrom(TryAllManager m, Location endLocation) {

            TryAllManager.DebugPrint("Dismissing update enlistments from {0} to {1}\n",
                                     __arglist(Location.ToDebugIdx(endLocation),
                                               Location.ToDebugIdx(CurrentLocation)));


            LogChunk startNode = this.currentChunk;
            LogChunk endNode = endLocation.node;
            int startEntry = startNode.nextEntry;
            int endEntry = endLocation.entry;

            if (startNode != endNode || startEntry != endEntry) {

                while (startNode != endNode) {
                    DismissChunkBetween(m, startNode, 0, startEntry);
                    startNode = startNode.next;
                    startEntry = startNode.nextEntry; //TryAllManager.ENLISTMENT_LOG_CHUNK_SIZE;
                }
                
                DismissChunkBetween(m, startNode, endEntry, startEntry);

#if ENABLE_BITMAP
                if (TryAllManager.BITMAP) {
                    for (int entry = endLocation.entry; entry < endNode.nextEntry; entry ++) {
                        endNode.entries[entry].bitmap0 = UIntPtr.Zero;
                        endNode.entries[entry].bitmap1 = UIntPtr.Zero;
                        endNode.entries[entry].bitmap2 = UIntPtr.Zero;
                        endNode.entries[entry].bitmap3 = UIntPtr.Zero;
                    }
                }
#endif
                
                this.currentChunk = endNode;
                this.currentChunk.nextEntry = endLocation.entry;
            }

            TryAllManager.DebugPrint("Current chunk={0:x} entries={1:x} nextEntry={2}\n",
                                     __arglist(Magic.addressOf(this.currentChunk),
                                               Magic.addressOf(this.currentChunk.entries),
                                               this.currentChunk.nextEntry));
        }


        // For each enlistment was log the version information we saw when we enlisted
        // the object.  For an update enlistment we need:
        //
        //  - A handle for the object in question
        //
        //  - The STMWord that was current when we enlisted it: this is needed
        //    (a) to compute the next version number when we stand down
        //    our enlistment and (b) to deal with the case where we
        //    enlist an object for read and then upgrade it to an update
        //    enlistment -- we check the value in the read log against the 
        //    value here.
        //
        //  - A pointer to our TryAllManager (used when we find a pointer to an
        //    Entry structure to tell if it's one of ours or someone else's).
        //
        //  - A pointer to the array of Entry structures that this is within.
        //    This is used during GC to avoid frequent use of interior pointers.
        // 
        // NB: we will eventually need 16-byte alignment anyway because of the 
        // 2 bits needed for the MUW tag, 1 bit needed for IS_OWNED_MASK and
        // 1 bit used to distinguish objects allocated within the current transaction.
        // We could remove the last two fields if the time writing them is prohibitive
        // (but note that they could be written when allocating a new chunk rather
        // than on every update enlistment).
        //
        // We use sequential layout because STMWord.Visit uses a hack to get
        // to the offset field.  This is necessary (at 16 Aug 05) to avoid asm
        // code like this being generated for the field access:
        //
        //     mov ebx,?Field offset : uintPtr

#if ENABLE_BITMAP
        [StructAlignAttribute(32), StructLayout(LayoutKind.Sequential)]
#else
        [StructAlignAttribute(16)]
#endif
        internal struct Entry {
            internal STMHandle h;
            internal STMWord v;
            internal UIntPtr m;
            internal UIntPtr offset;
#if ENABLE_BITMAP
            internal UIntPtr bitmap0;
            internal UIntPtr bitmap1;
            internal UIntPtr bitmap2;
            internal UIntPtr bitmap3;
#endif
        }

        internal class LogChunk {
            internal LogChunk(Entry[] entries,LogChunk next) {
                this.nextEntry = 0;
                this.entries = entries;
                this.next = next;
            }
        
            internal Entry[] entries;
            internal LogChunk next;
            internal int nextEntry;
        }
    

        internal unsafe void Dump() {
            VTable.DebugPrint("Enlistment log:\n");
            LogChunk chunk = this.currentChunk;
            int lowIdx = 0;
            int highIdx = chunk.nextEntry;

            while (chunk != null) {
                Entry[] entries = chunk.entries;
                VTable.DebugPrint("chunk={0} entries={1}\n",
                                  __arglist((uint)(Magic.addressOf(chunk)),
                                            (uint)(Magic.addressOf(entries))));

                for (int i = lowIdx; i < highIdx; i++) {
                    VTable.DebugPrint("entry[{0}] : <{1}> logged: <{2}> now: <{3}>\n",
                                      __arglist(i,
                                                (uint)(entries[i].h.addr),
                                                (uint)(entries[i].v.value),
                                                (uint)(entries[i].h.GetSTMSnapshot().GetSTMWord().value)));

                }

                chunk = chunk.next;
                highIdx = chunk.nextEntry;
            }
        }

        [NoInline]
        internal unsafe void AddCapacity(TryAllManager m) {
            m.tryAllCounters.IncrementEnlistmentOverflow();

            // NB: ensure links from the new chunk to the current one are in place
            // before linking it in -- the write barriers may cause GC and we 
            // need to find the log chunks.  

            Entry[] newEntries = 
                new Entry[TryAllManager.ENLISTMENT_LOG_CHUNK_SIZE];

            LogChunk newNode = 
                new LogChunk(newEntries, this.currentChunk);

            this.currentChunk = newNode;

            for (int i = 0; i < TryAllManager.ENLISTMENT_LOG_CHUNK_SIZE; i ++) {
                newEntries[i].m = Magic.addressOf(m);
                newEntries[i].offset = ((UIntPtr)AddrOfEntry(i)) - Magic.addressOf(newEntries);
            }
        }
    
        [InlineCopyAttribute]
        internal struct Location {
            internal Location(LogChunk node, int entry) {
                this.node = node;
                this.entry = entry;
            }
        
            internal static bool Eq(Location l1, Location l2) {
                return (l1.entry == l2.entry) && (l1.node == l2.node);
            }

            internal static int ToDebugIdx(Location l1) {
                LogChunk n1 = l1.node;
                int result = 0;

                while (n1.next != null) {
                    result += TryAllManager.ENLISTMENT_LOG_CHUNK_SIZE;
                    n1 = n1.next;
                }
                result += l1.entry;
                return result;
            }

            internal LogChunk node;
            internal int entry;
        }

        internal Location CurrentLocation {
            get {
                return new Location(this.currentChunk, this.currentChunk.nextEntry);
            }
        }

        internal int Size {
            get {
                int size = 0;
                for(LogChunk node = this.currentChunk;
                    node != null;
                    node = node.next) {
                    size += node.nextEntry;
                }
                return size;
            }
        }

#if !DEBUG
        [DisableBoundsChecks]
        [DisableNullChecks]
#endif // !DEBUG
        internal unsafe void VisitWeakRefs(TryAllManager m,
                                           DirectReferenceVisitor v) {
            LogChunk fromChunk = this.currentChunk;
            Entry[] fromEntries = fromChunk.entries;
            int fromEntry = fromChunk.nextEntry;
            int fromNumBlocks = 1;

            LogChunk toChunk = fromChunk;
            Entry[] toEntries = fromEntries;
            int toEntry = fromEntry;
            int toNumBlocks = 1;

            if (m.nextSavedTryAll == 0) {
                for (int i = 0; i < TryAllManager.ENLISTMENT_LOG_CHUNK_SIZE; i ++) {
                    toEntries[i].m = Magic.addressOf(m);
                }
            } else {
                for (int depth = m.nextSavedTryAll - 1; depth >= 0; depth --) {
                    LogChunk endFromChunk = m.savedTryAlls[0].uEnlistmentLogAtStart.node;
                    int endFromEntry = m.savedTryAlls[0].uEnlistmentLogAtStart.entry;
                    
                    TryAllManager.DebugPrintGC("Visiting update enlistments for {0:x} depth {1} {2:x} ({3:x}:{4})\n", 
                                               __arglist((UIntPtr)Magic.addressOf(m),
                                                         depth,
                                                         Magic.addressOf(fromChunk),
                                                         Magic.addressOf(endFromChunk),
                                                         endFromEntry));
                    
                    while (true) {
                        bool inEndChunk = (fromChunk == endFromChunk);
                        int downTo = inEndChunk ? endFromEntry : 0;
                        
                        for (fromEntry --; fromEntry >= downTo; fromEntry --) {
                            STMHandle h = fromEntries[fromEntry].h;
                            
                            TryAllManager.DebugPrintGC("saw index {0:x}/{1} {2:x} in update enlistments\n",
                                                       __arglist(Magic.addressOf(fromEntries),
                                                                 fromEntry,
                                                                 h.addr));
                            
                            if (h.addr != UIntPtr.Zero) {
                                if (fromEntries[fromEntry].h.Visit(v)) {
                                    // Move on to the next to-chunk if we've filled one
                                    if (toEntry == 0) {
                                        toChunk = toChunk.next;
                                        toEntries = toChunk.entries;
                                        toEntry = toEntries.Length;
                                        
                                        toChunk.nextEntry = toEntries.Length;
                                        toNumBlocks ++;
                                    }
                                    
                                    // Claim a slot in toEntries
                                    toEntry --;
                                    
                                    // Copy the entry to the to-chunk, visit the
                                    // pointer-derived values in it
                                    toEntries[toEntry].h = fromEntries[fromEntry].h;
                                    toEntries[toEntry].v = fromEntries[fromEntry].v;
                                    toEntries[toEntry].v.Visit(v);
                                    
#if ENABLE_BITMAP
                                    if (TryAllManager.BITMAP) {
                                        toEntries[toEntry].bitmap0 = fromEntries[fromEntry].bitmap0;
                                        toEntries[toEntry].bitmap1 = fromEntries[fromEntry].bitmap1;
                                        toEntries[toEntry].bitmap2 = fromEntries[fromEntry].bitmap2;
                                    } 
                                    
                                    if (TryAllManager.EXTERNAL_BITMAP) {
                                        toEntries[toEntry].bitmap3 = UIntPtr.Zero;
                                    }
#endif
                                    
                                    fixed (UpdateEnlistmentLog.Entry *toAddr = 
                                           &toEntries[toEntry]) {
                                        STMWord newWord = new STMWord((UIntPtr)toAddr, true);
                                        TryAllManager.DebugPrintGC("      word now {0:x}\n",
                                                                   __arglist(newWord.value));
                                        toEntries[toEntry].h.SetSTMWordAtGC(v, newWord);
                                    }
                                    
                                    TryAllManager.DebugPrintGC("   --> {0:x}/{1} {2:x}\n",
                                                               __arglist(Magic.addressOf(toEntries),
                                                                         toEntry,
                                                                         toEntries[toEntry].h.addr));
                                } else {
                                    TryAllManager.DebugPrintGC("   cleared weak ref\n");
                                    m.tryAllCounters.IncrementWeakRefsClearedInUpdateEnlistmentLog();
                                }
                            }
                        }
                        
                        for (int i = 0; i < TryAllManager.ENLISTMENT_LOG_CHUNK_SIZE; i ++) {
                            toEntries[i].m = Magic.addressOf(m);
                        }
                        
                        if (inEndChunk) {
                            break;
                        }
                        
                        TryAllManager.DebugPrintGC("Going on from {0:x} {1:x} {2:x}\n",
                                               __arglist(Magic.addressOf(fromChunk),
                                                         Magic.addressOf(fromEntries),
                                                         Magic.addressOf(fromChunk.next)));
                        
                        // Move on to the next from-chunk
                        fromChunk = fromChunk.next;
                        fromEntries = fromChunk.entries;
                        fromEntry = fromChunk.nextEntry;
                        fromNumBlocks ++;
                    } 
                    
                    // Update finishing point
                    TryAllManager.DebugPrintGC("Log now starts at {0:x}:{1}\n",
                                               __arglist(Magic.addressOf(toChunk),
                                                         toEntry));
                    m.savedTryAlls[depth].uEnlistmentLogAtStart.node = toChunk;
                    m.savedTryAlls[depth].uEnlistmentLogAtStart.entry = toEntry;
                }
                
                VTable.Assert(fromChunk.next == null);
                toChunk.next = null;
                
                if (TryAllManager.ENABLE_PROFILING) {
                    if (VTable.enableGCTiming) {
                        VTable.DebugPrint("[Update enlistment log: {0}->{1} * {2}]\n",
                                          __arglist(fromNumBlocks,
                                                    toNumBlocks,
                                                    TryAllManager.ENLISTMENT_LOG_CHUNK_SIZE));
                    }
                }
                
#if DEBUG
                for (int i = 0; i < toEntry; i ++) {
                    toEntries[i].h.addr = (UIntPtr)TryAllManager.DEAD_PTR;
                    toEntries[i].v.value = UIntPtr.Zero;
                }
#endif
            }
        }

        internal LogChunk currentChunk;
    }

    //----------------------------------------------------------------------
    //
    // Update log

    unsafe struct UpdateLogWriter {
        internal UpdateLog.Entry *next;
        internal UpdateLog.Entry *limit;

        internal unsafe UpdateLogWriter(UpdateLog.Entry *next,
                                        UpdateLog.Entry *limit) {
            this.next = next;
            this.limit = limit;
        }

        [Inline]
#if !DEBUG
        [DisableBoundsChecks]
        [DisableNullChecks]
#endif // !DEBUG
        internal static void EnsureLogMemory(TryAllManager m, uint bytesNeeded) {
            VTable.Assert(bytesNeeded <= TryAllManager.UPDATE_LOG_CHUNK_SIZE * sizeof(UpdateLog.Entry));
            TryAllManager.DebugPrint("Update: EnsureLogMemory : bytesNeeded={0}\n",
                                     __arglist(bytesNeeded));

            if((UIntPtr)m._updateLogWriter.next + bytesNeeded
                > (UIntPtr) m._updateLogWriter.limit) {
                 GetNewLogChunk(m);
             }             

        }

        [Inline]
#if !DEBUG
        [DisableBoundsChecks]
        [DisableNullChecks]
#endif // !DEBUG
        internal static void EnsureLogMemory(TryAllManager m) {
            TryAllManager.DebugPrint("Update: EnsureLogMemory\n");

            if((UIntPtr)m._updateLogWriter.next 
                > (UIntPtr) m._updateLogWriter.limit) {
                 GetNewLogChunk(m);
             }             

        }

        [NoInline]
        internal static unsafe void GetNewLogChunk(TryAllManager m) {
            // TryAllManager m = TryAllManager.CurrentRunningTryAll;
            UpdateLog.SyncFromWriter(m);
            m._updateLogWriter = UpdateLog.GetInvalidWriter();
            m.updateLog.AddCapacity(m);
            UpdateLog.InitWriter(m);
            
            TryAllManager.DebugPrint("UpdateLogWriter, entries[0]={0}\n",
                                     __arglist((uint)(UIntPtr *)(m._updateLogWriter.next)));
        }

#if !DEBUG
        [Inline] [DisableBoundsChecks] [DisableNullChecks]
#endif 
        internal static void Write(TryAllManager m, 
                                   UpdateLog.EntryKind kind,
                                   Object obj,
                                   UIntPtr offset,
                                   bool mayHaveObj,
                                   bool mustHaveObj,
                                   bool ensureAfter) {

            VTable.Deny(m._updateLogWriter.next > m._updateLogWriter.limit);

            if (mustHaveObj) {

                // NB: filtering depends on the updated-object log entries being
                // written
                if (!TryAllManager.DISABLE_BEFORE_WRITING_LOG
                    && (TryAllManager.TRACK_TRANSACTION_LOCALS
                        || TryAllManager.BITMAP)) {

                    STMHandle h = new STMHandle(obj);
                    STMSnapshot s = h.GetSTMSnapshot();

                    if (TryAllManager.TRACK_TRANSACTION_LOCALS) {
                        if (s.value == m.locallyAllocatedSTMWord.value) {
                            TryAllManager.DebugPrint("Not logging store to locally allocated obj {0:x}\n",
                                                     __arglist(Magic.addressOf(obj)));
                            m.tryAllCounters.IncrementLocalUpdate(kind);
                            return;
                        }
                    }

#if ENABLE_BITMAP
                    if (TryAllManager.BITMAP) {
                        uint wordOffset = (uint)offset >> 2;
                        STMWord w = s.GetSTMWord();
                        
                        // See known problem: this test could be removed
                        // at the cost of splitting the Log* operations into try_all
                        // and atomic variants.
                        if (w.IsOwned()) {
                            if (wordOffset < 96 || TryAllManager.DISABLE_BEFORE_WRITING_LOG) {
                                UpdateEnlistmentLog.Entry *e = (UpdateEnlistmentLog.Entry*)(w.GetPayloadWhenOwned());
                                UIntPtr *bm = &e->bitmap0;
                                {
                                    int bitmapWord = (int)wordOffset >> 5;
                                    uint bitmapBit = wordOffset/* & 31*/;
                                    uint bit = (uint)1 << (int)bitmapBit;
                                    UIntPtr *bmw = bm + bitmapWord;
                                    uint saw = (uint)*bmw;
                                    if ((saw & bit) != 0) {
                                        TryAllManager.DebugPrint("Bitmap hit {0} {1} {2} {3}\n",
                                                                 __arglist(Magic.addressOf(obj),
                                                                           offset,
                                                                           (int)kind,
                                                                           (UIntPtr)bm));
                                        m.tryAllCounters.IncrementUpdateHitInBitmap(kind);
                                    } else {
                                        TryAllManager.DebugPrint("Bitmap miss {0} {1} {2} {3}\n",
                                                                 __arglist(Magic.addressOf(obj),
                                                                           offset,
                                                                           (int)kind,
                                                                           (UIntPtr)bm));
                                        saw |= bit;
                                        *bmw = (UIntPtr)saw;
                                        ReallyWrite(m, kind, Magic.addressOf(obj), offset, ensureAfter);
                                    }
                                    return;
                                }       
                            } else {
                                if (TryAllManager.EXTERNAL_BITMAP) {
                                    UpdateEnlistmentLog.Entry *e = (UpdateEnlistmentLog.Entry*)(w.GetPayloadWhenOwned());
                                    UIntPtr *bm = (UIntPtr*)e->bitmap3;
                                    if (bm == null) {
                                        uint objByteSize = (uint)GCs.ObjectLayout.Sizeof(obj);
                                        uint bitmapLen = objByteSize / 32;
                                        uint[] bitmap = new uint[bitmapLen - 3];
                                        // GC may occur here, recover entry information
                                        h = new STMHandle(obj);
                                        s = h.GetSTMSnapshot();
                                        w = s.GetSTMWord();
                                        e = (UpdateEnlistmentLog.Entry*)(w.GetPayloadWhenOwned());
                                        bm = (UIntPtr*)Magic.addressOf(bitmap);
                                        e->bitmap3 = Magic.addressOf(bitmap);
                                        m.tryAllCounters.IncrementExternalBitmaps();
                                    }
                                    
                                    int bitmapWord = (int)wordOffset >> 5;
                                    uint bitmapBit = wordOffset/* & 31*/;
                                    uint bit = (uint)1 << (int)bitmapBit;
                                    UIntPtr *bmw = bm + bitmapWord;
                                    uint saw = (uint)*bmw;
                                    if ((saw & bit) != 0) {
                                        TryAllManager.DebugPrint("External bitmap hit {0} {1} {2}\n",
                                                                 __arglist(Magic.addressOf(obj),
                                                                           offset,
                                                                           (int)kind));
                                        m.tryAllCounters.IncrementUpdateHitInBitmap(kind);
                                    } else {
                                        TryAllManager.DebugPrint("Bitmap miss {0} {1} {2}\n",
                                                                 __arglist(Magic.addressOf(obj),
                                                                           offset,
                                                                           (int)kind));
                                        saw |= bit;
                                        *bmw = (UIntPtr)saw;
                                        ReallyWrite(m, kind, Magic.addressOf(obj), offset, ensureAfter);
                                    }
                                    return;
                                } else {
                                    m.tryAllCounters.IncrementBitmapOverflows();
                                    ReallyWrite(m, kind, Magic.addressOf(obj), offset, ensureAfter);
                                    return;
                                }
                            }
                        } else {
                            ReallyWrite(m, kind, Magic.addressOf(obj), offset, ensureAfter);
                            return;
                        }
                    }
#endif
                }
            }

            UIntPtr objAddr;
            if (mayHaveObj) {
                objAddr = Magic.addressOf(obj);
            } else {
                objAddr = UIntPtr.Zero;
            } 

            ReallyWrite(m, 
                        kind,
                        objAddr,
                        offset,
                        ensureAfter);
        }
        
#if !DEBUG
        [Inline] [DisableBoundsChecks] [DisableNullChecks]
#endif 
        internal static void ReallyWrite(TryAllManager m, 
                                         UpdateLog.EntryKind kind,
                                         UIntPtr objAddr,
                                         UIntPtr offset,
                                         bool ensureAfter) {
            if (TryAllManager.DISABLE_BEFORE_WRITING_LOG) {
                return;
            }
            
            TryAllManager.DebugPrint("Logging store to obj={0:x} offset={1} at {2:x}\n",
                                     __arglist(objAddr,
                                               offset,
                                               (uint)(UIntPtr)m._updateLogWriter.next));
            
            m.tryAllCounters.IncrementUpdateLogged(kind);
            TryAllManager.CountAsLogged();
            
            VTable.Deny(m._updateLogWriter.next > m._updateLogWriter.limit);
            
            UpdateLog.Entry *ne = m._updateLogWriter.next;
            ne -> kind = kind;
            ne -> obj = objAddr;
            ne -> offset = offset;
            ne -> val = *(UIntPtr*)(objAddr + offset);
            ne++;
            m._updateLogWriter.next = ne;
            
            //------------------------------------------------------------------
            
            if (ensureAfter) {
                EnsureLogMemory(m);
            }
        }

        //......................................................................
    }

    [NoLoggingForUndo]
    class UpdateLog {
        internal UpdateLog() {
            Entry[] entries = new Entry[TryAllManager.UPDATE_LOG_CHUNK_SIZE];
            this.currentChunk = new LogChunk(entries, null);
        }

#if !DEBUG
        [DisableBoundsChecks]
        [DisableNullChecks]
#endif // !DEBUG
        internal static unsafe void SyncFromWriter(TryAllManager m) {
            UpdateLog l = m.updateLog;

            if (m._updateLogWriter.next != null) { 
                l.currentChunk.nextEntry = (int)l.AddrToIndex(m._updateLogWriter.next);
            } 

            VTable.Assert(l.currentChunk.nextEntry >= 0);
            VTable.Assert(l.currentChunk.nextEntry <= TryAllManager.UPDATE_LOG_CHUNK_SIZE);

            TryAllManager.DebugPrint("UpdateLogWriter : sync when nextExntry={0}\n",
                                     __arglist(l.currentChunk.nextEntry));
        }
      
        internal static unsafe UpdateLogWriter GetInvalidWriter() {
            return new UpdateLogWriter(null, null);
        }

#if !DEBUG
        [DisableBoundsChecks]
        [DisableNullChecks]
#endif // !DEBUG
        internal static unsafe bool WriterIsValid(UpdateLogWriter w) {
            return (w.next != null);
        }

#if !DEBUG
        [DisableBoundsChecks]
        [DisableNullChecks]
#endif // !DEBUG
        internal static unsafe void InitWriter(TryAllManager m) {
            UpdateLog u = m.updateLog;
            Entry *next = u.AddrOfEntry(u.currentChunk.nextEntry);
            Entry *limit = u.AddrOfEntry(TryAllManager.UPDATE_LOG_CHUNK_SIZE - 1);
            
            TryAllManager.DebugPrint("UpdateLogWriter : nextEntry={0} next={1} limit={2}\n",
                                     __arglist(u.currentChunk.nextEntry,
                                               (uint)(UIntPtr)next,
                                               (uint)(UIntPtr)limit));

            m._updateLogWriter.next = next;
            m._updateLogWriter.limit = limit;
        }

        // TODO: Inliner will not inline this method because of the pinned var
        // (and will warn repeatedly about it).
        //[Inline]
#if !DEBUG
        [DisableBoundsChecks]
        [DisableNullChecks]
#endif // !DEBUG
        internal unsafe Entry *AddrOfEntry(int idx) {
            Entry[] entries = this.currentChunk.entries;
            UIntPtr addrAsUIntPtr;
            Entry *result;

            fixed (Entry *baseAddr = &entries[0]) {
                Entry *entryAddr = baseAddr + idx;
                addrAsUIntPtr = (UIntPtr) entryAddr;
            }

            result = (Entry *) addrAsUIntPtr;

            return result;
        }
      
        // TODO: Inliner will not inline this method because of the pinned var
        // (and will warn repeatedly about it).
        //[Inline]
#if !DEBUG
        [DisableBoundsChecks]
        [DisableNullChecks]
#endif // !DEBUG
        internal unsafe uint AddrToIndex(Entry *entryPtr) {
            uint result;
            UIntPtr baseAddr;
            fixed (Entry *basePtr = &this.currentChunk.entries[0]) {
                baseAddr = (UIntPtr)basePtr;
            }
            UIntPtr entryAddr = (UIntPtr)entryPtr;
            result = (uint)((int)(entryAddr - baseAddr)) / ((uint)sizeof (Entry));
            return (uint)result;
        }

        // The Entry struct is the struct holding individual log entries.
        //
        // Discipline note: when setting, always set obj first, then offset.  when
        // clearing, always clear offset first, then obj.

        internal enum EntryKind {
            HEAP_VAL,
            HEAP_REF,
            NON_HEAP_VAL,
            NON_HEAP_REF
        }

        internal struct Entry {
            internal EntryKind kind; // Could use spare bits in obj
            internal UIntPtr obj;    // Really of type Object
            internal UIntPtr offset;
            internal UIntPtr val;
        }

        internal class LogChunk {
            internal LogChunk(Entry[] entries,LogChunk next) {
                this.entries = entries;
                this.next = next;
                this.nextEntry = 0;
            }

            internal Entry[] entries;
            internal LogChunk next;
            internal int nextEntry = 0;
        }

        [Inline]
        internal void ResetTo(Location l1) {
            this.currentChunk = l1.node;
            this.currentChunk.nextEntry = l1.entry;
        }

        [Inline]
        internal void AddCapacity(TryAllManager m) {
          
            m.tryAllCounters.IncrementUpdateOverflow();

            // NB: construct these objects before linking them incase the write
            // barriers cause GC.
            Entry[] newEntries = new Entry[TryAllManager.UPDATE_LOG_CHUNK_SIZE];
            LogChunk newNode = new LogChunk(newEntries, this.currentChunk);

            this.currentChunk = newNode;
        }

        [InlineCopyAttribute]
        internal struct Location {
            internal Location(LogChunk node, int entry) {
                this.node = node;
                this.entry = entry;
            }

            internal static int ToDebugIdx(Location l1) {
                LogChunk n1 = l1.node;
                int result = 0;

                while (n1.next != null) {
                    result += TryAllManager.UPDATE_LOG_CHUNK_SIZE;
                    n1 = n1.next;
                }
                result += l1.entry;
                return result;
            }

            internal bool LtEq(Location other) {
                LogChunk n1 = this.node;
                LogChunk n2 = other.node;
                if(n1 == n2) {
                    return this.entry <= other.entry;
                }
                while(n2 != null) {
                    n2 = n2.next;
                    if(n1 == n2) {
                        return true;
                    }
                }
                return false;
            }

            internal LogChunk node;
            internal int entry;
        }

        internal Location CurrentLocation {
            get {
                return new Location(this.currentChunk, this.currentChunk.nextEntry);
            }
        }

        internal int Size {
            get {
                int size = 0;
                for(LogChunk node = this.currentChunk;
                    node != null;
                    node = node.next) {
                    size += node.nextEntry;
                }
                return size;
            }
        }

        internal unsafe void Dump() {
            VTable.DebugPrint("Update log:\n");
            LogChunk chunk = this.currentChunk;
            int highIdx = chunk.nextEntry;
            int lowIdx = 0;

            while (chunk != null) {
                Entry[] entries = chunk.entries;
                VTable.DebugPrint("chunk={0} entries={1}\n",
                                  __arglist((uint)(Magic.addressOf(chunk)),
                                            (uint)(Magic.addressOf(entries))));
                
                for (int i = lowIdx; i < highIdx; i++) {
                    UIntPtr cur;
                    cur = *TryAllManager.getLoc(Magic.fromAddress(entries[i].obj), 
                                                entries[i].offset);
                    VTable.DebugPrint("entry[{0}] : {1} obj: {2} offset: {3} val: {4} now: {5}\n",
                                      __arglist(i,
                                                (uint)(entries[i].kind),
                                                (uint)(entries[i].obj),
                                                (uint)(entries[i].offset),
                                                (uint)(entries[i].val),
                                                (uint)cur));
                }

                chunk = chunk.next;
                highIdx = chunk.nextEntry;
            }
        }

        internal void RollBack(TryAllManager m, 
                               StackHeight stackHeight, 
                               Location endLocation) {

            //
            // Undo the entries from end block back to start block
            //

            TryAllManager.DebugPrint("Rolling back from {0} to {1}\nCurrent stack height is {2}\n",
                                     __arglist(Location.ToDebugIdx(endLocation),
                                               Location.ToDebugIdx(CurrentLocation),
                                               stackHeight.ToString()));


            VTable.Assert(endLocation.LtEq(this.CurrentLocation));

            LogChunk endNode = endLocation.node;

            LogChunk startNode = this.currentChunk;
            int startEntry = startNode.nextEntry - 1;
            Entry[] entries = startNode.entries;

            do {
                int endEntry = (startNode == endNode) ? endLocation.entry : 0;
                for (int entry = startEntry; entry >= endEntry; entry--) {
                    TryAllManager.DebugPrint("Rolling back kind={0} obj={1} offset={2} val={3}\n",
                                             __arglist((int)(entries[entry].kind),
                                                       (uint)(entries[entry].obj),
                                                       (uint)(entries[entry].offset),
                                                       (uint)(entries[entry].val)));

                    if (entries[entry].obj == UIntPtr.Zero &&
                        entries[entry].offset == UIntPtr.Zero) {
                        VTable.DebugPrint("Saw null'd ref in update log\n");
                    } else {
                        switch (entries[entry].kind) {
                        case EntryKind.HEAP_VAL:
                            TryAllManager.setAt(Magic.fromAddress(entries[entry].obj),
                                                entries[entry].offset,
                                                entries[entry].val);
                            break;
                            
                        case EntryKind.NON_HEAP_VAL:
                            TryAllManager.setAtStack(stackHeight,
                                                     null,
                                                     entries[entry].offset,
                                                     entries[entry].val);
                            break;
                            
                        case EntryKind.HEAP_REF:
                            TryAllManager.setAt(Magic.fromAddress(entries[entry].obj),
                                                entries[entry].offset,
                                                Magic.fromAddress(entries[entry].val));
                            break;
                            
                        case EntryKind.NON_HEAP_REF:
                            TryAllManager.setAtStack
                                (stackHeight,
                                 null,
                                 entries[entry].offset,
                                 Magic.fromAddress(entries[entry].val));
                            break;
                            
                        default:
                            TryAllManager.DebugPrintNoLock("Unexpected kind {0}",
                                                           __arglist((int)(entries[entry].kind)));
                            VTable.DebugBreak();
                            break;
                        }
                    }
                }

                if (startNode == endNode) {
                    break;
                } else {
                    startNode = startNode.next;
                    entries = startNode.entries;
                    startEntry = startNode.nextEntry - 1;
                }
            } while (true);
            

            this.currentChunk = endNode;
            this.currentChunk.nextEntry = endLocation.entry;
        }

#if !DEBUG
        [DisableBoundsChecks]
        [DisableNullChecks]
#endif // !DEBUG
        internal unsafe void VisitStrongRefs(TryAllManager m, DirectReferenceVisitor v)
        {
            LogChunk chunk = TryAllManager.toUpdateLogChunk(TryAllManager.ReadBarrier(v, 
                                                                                      this.currentChunk));
            
#if ENABLE_GC_TRACING
            VTable.DebugPrint("Visiting updates logged for {0:x} (strong)\n",
                              __arglist(Magic.addressOf(m)));
#endif
            Entry[] entries = TryAllManager.toUpdateLogEntryArray(TryAllManager.ReadBarrier(v, chunk.entries));

            int endEntry = chunk.nextEntry;
            int numBlocks = 0;
            
            do {
                numBlocks++;
#if ENABLE_GC_TRACING
                VTable.DebugPrint("block={0} entries={1}\n",
                                  __arglist((int)Magic.addressOf(chunk),
                                            (int)Magic.addressOf(entries)));
#endif
                for (int entry = 0; entry < endEntry; entry++) {
                    EntryKind k = entries[entry].kind;
                    
                    // Visit the overwritten value if it has a pointer type
                    if (k == EntryKind.HEAP_REF || k == EntryKind.NON_HEAP_REF) {
                        fixed(UIntPtr* pobj = &entries[entry].val) {
                            if(*pobj != UIntPtr.Zero) {
                                v.Visit(pobj);
                            }
                        }
                    }
                }
                LogChunk next = TryAllManager.toUpdateLogChunk(TryAllManager.ReadBarrier(v, chunk.next));
                if (next == null) break;
                chunk = next;

                entries = TryAllManager.toUpdateLogEntryArray(TryAllManager.ReadBarrier(v, chunk.entries));
                endEntry = chunk.nextEntry;
            } while (true);

            if (TryAllManager.ENABLE_PROFILING) {
                if (VTable.enableGCTiming) {
                    VTable.DebugPrint("[Update log: {0} * {1}]\n",
                                      __arglist(numBlocks,
                                                TryAllManager.UPDATE_LOG_CHUNK_SIZE));
                }
            }
        }

#if !DEBUG
        [DisableBoundsChecks]
        [DisableNullChecks]
#endif // !DEBUG
        internal unsafe void VisitWeakRefs(TryAllManager m,
                                           DirectReferenceVisitor rv) {
            LogChunk fromChunk = this.currentChunk;
            Entry[] fromEntries = fromChunk.entries;
            int fromEntry = fromChunk.nextEntry;
            int fromNumBlocks = 1;

            LogChunk toChunk = fromChunk;
            Entry[] toEntries = fromEntries;
            int toEntry = fromEntry;
            int toNumBlocks = 1;

            for (int depth = m.nextSavedTryAll - 1; depth >= 0; depth --) {
                LogChunk endFromChunk = m.savedTryAlls[depth].updateLogAtStart.node;
                int endFromEntry = m.savedTryAlls[depth].updateLogAtStart.entry;
                
                TryAllManager.DebugPrintGC("Visiting updates for {0:x} depth {1} ({2:x}:{3})\n", 
                                    __arglist((UIntPtr)Magic.addressOf(m),
                                              depth,
                                              Magic.addressOf(endFromChunk),
                                              endFromEntry));
                
                while (true) {
                    bool inEndChunk = (fromChunk == endFromChunk);
                    int downTo = inEndChunk ? endFromEntry : 0;
                    
                    for (fromEntry --; fromEntry >= downTo; fromEntry --) {
                        
                        TryAllManager.DebugPrintGC("saw index {0:x}/{1} {2}+{3} in update log\n",
                                            __arglist(Magic.addressOf(fromEntries),
                                                      fromEntry,
                                                      fromEntries[fromEntry].obj,
                                                      fromEntries[fromEntry].offset));
                        
                        EntryKind k = fromEntries[fromEntry].kind;
                        bool keep = true;
                        if (k == EntryKind.HEAP_VAL || k == EntryKind.HEAP_REF) {
                            fixed(UIntPtr* pobj = &fromEntries[fromEntry].obj) {
                                if(*pobj != UIntPtr.Zero) {
                                    rv.Visit(pobj);
                                    if (*pobj == UIntPtr.Zero) {
                                        TryAllManager.DebugPrintGC("   cleared weak ref\n");
                                        m.tryAllCounters.IncrementWeakRefsClearedInUpdateLog();
                                        keep = false;
                                    }
                                }
                            }
                        }
                        
                        if (keep) {
                            // Move on to the next to-chunk if we've filled one
                            if (toEntry == 0) {
                                toChunk = toChunk.next;
                                toEntries = toChunk.entries;
                                toEntry = toEntries.Length;
                                
                                toChunk.nextEntry = toEntries.Length;
                                toNumBlocks ++;
                            }
                            
                            // Claim a slot in toEntries
                            toEntry --;
                            
                            // Copy the entry to the to-chunk, visit the
                            // pointer-derived values in it
                            toEntries[toEntry] = fromEntries[fromEntry];
                            
                            TryAllManager.DebugPrintGC("   --> {0:x}/{1} {2:x}+{3}\n",
                                              __arglist(Magic.addressOf(toEntries),
                                                        toEntry,
                                                        toEntries[toEntry].obj,
                                                        toEntries[toEntry].offset));
                        }
                    }

                    if (inEndChunk) {
                        break;
                    }
                    
                    // Move on to the next from-chunk
                    fromChunk = fromChunk.next;
                    fromEntries = fromChunk.entries;
                    fromEntry = fromChunk.nextEntry;
                    fromNumBlocks ++;
                }
                
                // Update finishing point
                TryAllManager.DebugPrintGC("Log now starts at {0:x}:{1}\n",
                                           __arglist(Magic.addressOf(toChunk),
                                                     toEntry));
                m.savedTryAlls[depth].updateLogAtStart.node = toChunk;
                m.savedTryAlls[depth].updateLogAtStart.entry = toEntry;
            }

            VTable.Assert(fromChunk.next == null);
            toChunk.next = null;

            if (TryAllManager.ENABLE_PROFILING) {
                if (VTable.enableGCTiming) {
                    VTable.DebugPrint("[Update log: {0}->{1} * {2}]\n",
                                      __arglist(fromNumBlocks,
                                                toNumBlocks,
                                                TryAllManager.UPDATE_LOG_CHUNK_SIZE));
                }
            }

#if DEBUG
            for (int i = 0; i < toEntry; i ++) {
                toEntries[i].kind = EntryKind.HEAP_VAL;
                toEntries[i].obj = (UIntPtr)TryAllManager.DEAD_PTR;
                toEntries[i].offset = UIntPtr.Zero;
                toEntries[i].val = UIntPtr.Zero;
            }
#endif
        }

        internal LogChunk currentChunk;
    }

    //----------------------------------------------------------------------
    //
    // Undo log

    [NoLoggingForUndo]
    class UndoLog {
        internal UndoLog() {
            this.entries = new LogEntryUndoAction[TryAllManager.UNDO_INITIAL_SIZE];
        }

        [Inline]
        internal void Reset() {
            if (this.nextEntry != 0) {
                for(int i=0; i<this.nextEntry;++i) {
                    this.entries[i].UndoAction = null;
                }
                this.nextEntry = 0;
            }
        }

        internal void EnsureCapacity() {
            if (this.nextEntry >= this.entries.Length) {
                LogEntryUndoAction[] temp =
                    new LogEntryUndoAction[2 * this.entries.Length];
                Array.Copy(this.entries, 0, temp, 0, this.entries.Length);
                this.entries = temp;
            }
        }

        internal int Size {
            get {
                return this.nextEntry;
            }
        }

        internal int nextEntry;
        internal LogEntryUndoAction[] entries;
    }
  
    //----------------------------------------------------------------------
    //
    // Profiling counters

    [NoLoggingForUndo]
    [CCtorIsRunDuringStartup]
    sealed class TryAllCounters {
        private TryAllCounters() {
            // Create instances through NewRegisteredCounters
        }

        internal static TryAllCounters TryAllCountersList = null;
        internal static Object TryAllCountersLock = new Object();

        internal static TryAllCounters NewRegisteredCounters() {
            TryAllCounters c = new TryAllCounters();
            lock (TryAllCountersLock) {
                c.next = TryAllCountersList;
                TryAllCountersList = c;
            }
            return c;
        }

        internal static void DumpRegisteredCounters() {
            TryAllCounters c = new TryAllCounters();
            TryAllCounters temp = TryAllCountersList;
            while (temp != null) {
                c.MergeCounters(temp);
                temp = temp.next;
            }
            c.DumpStats();
        }

        internal void MergeCounters(TryAllCounters other) {
            this.startTryAll += other.startTryAll;
            this.commitSucceeded += other.commitSucceeded;

            this.ensureLogMemoryForUpdateEnlistmentLogCalls += 
                other.ensureLogMemoryForUpdateEnlistmentLogCalls;
            this.ensureLogMemoryForUpdateEnlistmentLogSlots += 
                other.ensureLogMemoryForUpdateEnlistmentLogSlots;
            this.ensureLogMemoryForReadEnlistmentLogCalls += 
                other.ensureLogMemoryForReadEnlistmentLogCalls;
            this.ensureLogMemoryForReadEnlistmentLogSlots += 
                other.ensureLogMemoryForReadEnlistmentLogSlots;
            this.ensureLogMemoryForUpdateLogCalls += 
                other.ensureLogMemoryForUpdateLogCalls;
            this.ensureLogMemoryForUpdateLogSlots += 
                other.ensureLogMemoryForUpdateLogSlots;

            this.logValHeapMultiple += other.logValHeapMultiple;
            this.logValHeap += other.logValHeap;
            this.logRefHeap += other.logRefHeap;
            this.logIndirectValMultiple += other.logIndirectValMultiple;
            this.logIndirectValHeap += other.logIndirectValHeap;
            this.logIndirectValStack += other.logIndirectValStack;
            this.logIndirectRefHeap += other.logIndirectRefHeap;
            this.logIndirectRefStack += other.logIndirectRefStack;

            this.logValHeapMultipleFast += other.logValHeapMultipleFast;
            this.logValHeapFast += other.logValHeapFast;
            this.logRefHeapFast += other.logRefHeapFast;
            this.logIndirectValMultipleFast += other.logIndirectValMultipleFast;
            this.logIndirectValHeapFast += other.logIndirectValHeapFast;
            this.logIndirectValStackFast += other.logIndirectValStackFast;
            this.logIndirectRefHeapFast += other.logIndirectRefHeapFast;
            this.logIndirectRefStackFast += other.logIndirectRefStackFast;

            this.skipScan += other.skipScan;
            this.enlistObjForRead += other.enlistObjForRead;
            this.enlistObjForUpdate += other.enlistObjForUpdate;
            this.enlistNewObjForUpdate += other.enlistNewObjForUpdate;
            this.enlistAddrForRead += other.enlistAddrForRead;
            this.enlistAddrForUpdate += other.enlistAddrForUpdate;
            this.enlistIndirectForRead += other.enlistIndirectForRead;
            this.enlistIndirectForUpdate += other.enlistIndirectForUpdate;

            this.enlistObjForReadFast += other.enlistObjForReadFast;
            this.enlistObjForUpdateFast += other.enlistObjForUpdateFast;
            this.enlistNewObjForUpdateFast += other.enlistNewObjForUpdateFast;
            this.enlistAddrForReadFast += other.enlistAddrForReadFast;
            this.enlistAddrForUpdateFast += other.enlistAddrForUpdateFast;
            this.enlistIndirectForReadFast += other.enlistIndirectForReadFast;
            this.enlistIndirectForUpdateFast += other.enlistIndirectForUpdateFast;

            this.invalidShake += other.invalidShake;
            this.invalidShakeException += other.invalidShakeException;
            this.invalidConflict += other.invalidConflict;
            this.invalidRace += other.invalidRace;
            this.invalidDuringGC += other.invalidDuringGC;
            this.invalidOutsideGC += other.invalidOutsideGC;
            this.inflationSeen += other.inflationSeen;
            this.updateOverflow += other.updateOverflow;
            this.enlistmentOverflow += other.enlistmentOverflow;
            this.loggedHeapVal += other.loggedHeapVal;
            this.loggedHeapRef += other.loggedHeapRef;
            this.loggedNonHeapVal += other.loggedNonHeapVal;
            this.loggedNonHeapRef += other.loggedNonHeapRef;
            this.localUpdateHeapVal += other.localUpdateHeapVal;
            this.localUpdateHeapRef += other.localUpdateHeapRef;
            this.localUpdateNonHeapVal += other.localUpdateNonHeapVal;
            this.localUpdateNonHeapRef += other.localUpdateNonHeapRef;
            this.updateHitInCacheHeapVal += other.updateHitInCacheHeapVal;
            this.updateHitInCacheHeapRef += other.updateHitInCacheHeapRef;
            this.updateHitInCacheNonHeapVal += other.updateHitInCacheNonHeapVal;
            this.updateHitInCacheNonHeapRef += other.updateHitInCacheNonHeapRef;
            this.updateHitInBitmapHeapVal += other.updateHitInBitmapHeapVal;
            this.updateHitInBitmapHeapRef += other.updateHitInBitmapHeapRef;
            this.updateHitInBitmapNonHeapVal += other.updateHitInBitmapNonHeapVal;
            this.updateHitInBitmapNonHeapRef += other.updateHitInBitmapNonHeapRef;
            this.enlistForReadLogged += other.enlistForReadLogged;
            this.enlistForUpdateLogged += other.enlistForUpdateLogged;
            this.readsHitInCache += other.readsHitInCache;
            this.cachesCreated += other.cachesCreated;
            this.bitmapOverflows += other.bitmapOverflows;
            this.externalBitmaps += other.externalBitmaps;
            this.forcedGC += other.forcedGC;
            this.weakRefsClearedInReadEnlistmentLog += other.weakRefsClearedInReadEnlistmentLog;
            this.weakRefsClearedInUpdateEnlistmentLog += other.weakRefsClearedInUpdateEnlistmentLog;
            this.weakRefsClearedInUpdateLog += other.weakRefsClearedInUpdateLog;
            this.readDuplicatesRemoved += other.readDuplicatesRemoved;
            this.updatesInReadEnlistmentsAtGC += other.updatesInReadEnlistmentsAtGC;
            this.updatesInReadEnlistmentsAtEnlistment += other.updatesInReadEnlistmentsAtEnlistment;
        }

        internal void DumpStats() {
            if (TryAllManager.ENABLE_PROFILING) {
            
            // NB: do not assert that total started == total ended because a
            // forced exit may occur when some threads are in the middle of 
            // transactions.
VTable.DebugPrint(@"
Total started:                {0}
Total ended:                  {1}
Of which:
   commitSucceeded:           {2}
   invalidShake:              {3}
   invalidShakeException:     {4}
   invalidConflict:           {5}
   invalidRace:               {6}
", __arglist(startTryAll, // 0
             (commitSucceeded + 
              invalidShake + 
              invalidShakeException + 
              invalidConflict + 
              invalidRace), // 1
             commitSucceeded, // 2
             invalidShake, // 3
             invalidShakeException, // 4
             invalidConflict, // 5
             invalidRace // 6
));

VTable.DebugPrint(@"
logValHeapMultiple:           {0}
logValHeap:                   {1}
logRefHeap:                   {2}
logIndirectValMultiple:       {3}
logIndirectValHeap:           {4}
logIndirectValHeap:           {5}
logIndirectRefHeap:           {6}
logIndirectRefStack:          {7}
",
__arglist(logValHeapMultiple, // 0
          logValHeap, // 1
          logRefHeap, // 2
          logIndirectValMultiple, // 3
          logIndirectValHeap, // 4
          logIndirectValStack, // 5
          logIndirectRefHeap, // 6
          logIndirectRefStack) // 7
);

VTable.DebugPrint(@"
logValHeapMultipleFast:       {0}
logValHeapFast:               {1}
logRefHeapFast:               {2}
logIndirectValMultipleFast:   {3}
logIndirectValHeapFast:       {4}
logIndirectValHeapFast:       {5}
logIndirectRefHeapFast:       {6}
logIndirectRefStackFast:      {7}
",
__arglist(logValHeapMultipleFast, // 0
          logValHeapFast, // 1
          logRefHeapFast, // 2
          logIndirectValMultipleFast, // 3
          logIndirectValHeapFast, // 4
          logIndirectValStackFast, // 5
          logIndirectRefHeapFast, // 6
          logIndirectRefStackFast  // 7
));

VTable.DebugPrint(@"
  HEAP_VAL total              {0}
  HEAP_VAL to local obj       {1}
  HEAP_VAL hit in table       {2}
  HEAP_VAL hit in bitmap      {3}
  HEAP_VAL logged             {4} ({5} %)

  HEAP_REF total              {6}
  HEAP_REF to local obj       {7}
  HEAP_REF hit in table       {8}
  HEAP_REF hit in bitmap      {9}
  HEAP_REF logged             {10} ({11} %)

  NON_HEAP_VAL total          {12}
  NON_HEAP_VAL to local obj   {13}
  NON_HEAP_VAL hit in table   {14}
  NON_HEAP_VAL hit in bitmap  {15}
  NON_HEAP_VAL logged         {16} ({17} %)

  NON_HEAP_REF total          {18}
  NON_HEAP_REF to local obj   {19}
  NON_HEAP_REF hit in table   {20}
  NON_HEAP_REF hit in bitmap  {21}
  NON_HEAP_REF logged         {22} ({23} %)

  readsHitInCache             {24}
  cachesCreated               {25}
  bitmapOverflows             {26}
  externalBitmaps             {27}
",
__arglist(
          logValHeap 
          + logIndirectValHeap 
          + logValHeapFast 
          + logIndirectValHeapFast, // 0
          localUpdateHeapVal, // 1
          updateHitInCacheHeapVal, // 2
          updateHitInBitmapHeapVal, // 3
          loggedHeapVal, // 4
          loggedHeapVal == 0 ? 0
                : ((100 * (long)loggedHeapVal)
                   / (logValHeap 
                      + logIndirectValHeap 
                      + logValHeapFast 
                      + logIndirectValHeapFast)), // 5

          logRefHeap 
          + logIndirectRefHeap
          + logRefHeapFast 
          + logIndirectRefHeapFast, // 6
          localUpdateHeapRef, // 7
          updateHitInCacheHeapRef, // 8
          updateHitInBitmapHeapRef, // 9
          loggedHeapRef, // 10
          loggedHeapRef == 0 ? 0
                : ((100 * (long)loggedHeapRef)
                   / ( logRefHeap 
                       + logIndirectRefHeap
                       + logRefHeapFast 
                       + logIndirectRefHeapFast)), // 11

          logIndirectValStack + logIndirectValStackFast, // 12
          localUpdateNonHeapVal, // 13
          updateHitInCacheNonHeapVal, // 14
          updateHitInBitmapNonHeapVal, // 15
          loggedNonHeapVal, // 16
          loggedNonHeapVal == 0 ? 0
                : ((100 * (long)loggedNonHeapVal)
                   / (logIndirectValStack + logIndirectValStackFast)), // 17

          logIndirectRefStack + logIndirectRefStackFast, // 18
          localUpdateNonHeapRef, // 19
          updateHitInCacheNonHeapRef, // 20
          updateHitInBitmapNonHeapRef, // 21
          loggedNonHeapRef, // 22
          loggedNonHeapRef == 0 ? 0
          : ((100 * (long)loggedNonHeapRef)
             / (logIndirectRefStack + logIndirectRefStackFast)), // 23

          readsHitInCache, // 24
          cachesCreated, // 25
          bitmapOverflows, // 26
          externalBitmaps) // 27
);
             
VTable.DebugPrint(@"
enlistObjForRead:             {0}
enlistAddrForRead:            {1}
  of which indirect:          {2}
  enlistForRead total:        {3}

enlistObjForUpdate:           {4}
enlistNewObjForUpdate:        {5}
enlistAddrForUpdate:          {6}
  of which indirect:          {7}
  enlistForUpdate total:      {8}
", __arglist(enlistObjForRead, // 0
             enlistAddrForRead, // 1
             enlistIndirectForRead, // 2
             enlistObjForRead + enlistAddrForRead, // 3

             enlistObjForUpdate, // 4
             enlistNewObjForUpdate, // 5
             enlistAddrForUpdate, // 6
             enlistIndirectForUpdate, // 7
             enlistObjForUpdate + enlistNewObjForUpdate + enlistAddrForUpdate // 9
));

VTable.DebugPrint(@"
enlistObjForReadFast:         {0}
enlistAddrForReadFast:        {1}
  of which indirect:          {2}
  enlistForReadFast total:    {3}

enlistObjForUpdateFast:       {4}
enlistNewObjForUpdateFast:    {5}
enlistAddrForUpdateFast:      {6}
  of which indirect:          {7}
  enlistForUpdateFast total:  {8}
", __arglist(enlistObjForReadFast, // 0
             enlistAddrForReadFast, // 1
             enlistIndirectForReadFast, // 2
             enlistObjForReadFast + enlistAddrForReadFast, //3

             enlistObjForUpdateFast, // 4
             enlistNewObjForUpdateFast, // 5
             enlistAddrForUpdateFast, // 6
             enlistIndirectForUpdateFast, // 7
             enlistObjForUpdateFast + enlistNewObjForUpdateFast + enlistAddrForUpdateFast // 8
));

VTable.DebugPrint(@"
enlistForRead logged:         {0} ({1} %)
enlistForUpdate logged:       {2} ({3} %)

", __arglist(enlistForReadLogged, // 0
             (enlistForReadLogged == 0 
              || (0 == (enlistObjForRead 
                        + enlistAddrForRead 
                        + enlistObjForReadFast 
                        + enlistAddrForReadFast))) 
             ? 0
             : ((100 * (long)enlistForReadLogged)
                / (enlistObjForRead 
                   + enlistAddrForRead 
                   + enlistObjForReadFast 
                   + enlistAddrForReadFast)), // 1

             enlistForUpdateLogged, // 2
             (enlistForUpdateLogged == 0
              || (0 == (enlistObjForUpdate
                        + enlistNewObjForUpdate
                        + enlistAddrForUpdate
                        + enlistObjForUpdateFast
                        + enlistNewObjForUpdateFast
                        + enlistAddrForUpdateFast)))
             ? 0
             : ((100 * (long)enlistForUpdateLogged)
                / (enlistObjForUpdate
                   + enlistNewObjForUpdate
                   + enlistAddrForUpdate
                   + enlistObjForUpdateFast
                   + enlistNewObjForUpdateFast
                   + enlistAddrForUpdateFast)) // 3
));

VTable.DebugPrint(@"
EnsureLogMemory:          Calls     Slots   
  UpdateEnlistmentLog:   {0,10} {1,10}
  ReadEnlistmentLog:     {2,10} {3,10}
  UpdateLog:             {4,10} {5,10}
", __arglist(ensureLogMemoryForUpdateEnlistmentLogCalls, // 0
             ensureLogMemoryForUpdateEnlistmentLogSlots, // 1
             ensureLogMemoryForReadEnlistmentLogCalls, // 2
             ensureLogMemoryForReadEnlistmentLogSlots, // 3
             ensureLogMemoryForUpdateLogCalls, // 4
             ensureLogMemoryForUpdateLogSlots // 5
)); 

VTable.DebugPrint(@"
invalidDuringGC:              {0}
updateOverflow:               {1}
enlistmentOverflow:           {2}
newBytesSinceGC:              {3}
", __arglist(invalidDuringGC, // 0
             updateOverflow, // 1
             enlistmentOverflow, // 2
             (int)BaseCollector.DebugNewBytesSinceGC // 3
));

VTable.DebugPrint(@"
Weak refs cleared in:
  ReadEnlistmentLog:          {0}
  UpdateEnlistmentLog:        {1}
  UpdateLog:                  {2}
", __arglist(weakRefsClearedInReadEnlistmentLog, // 0
             weakRefsClearedInUpdateEnlistmentLog, // 1
             weakRefsClearedInUpdateLog // 2
));

VTable.DebugPrint(@"
Duplicate reads removed:      {0}
RMW removed at GC:            {1}
RMW removed at enlistment:    {2}
", __arglist(readDuplicatesRemoved, // 0
             updatesInReadEnlistmentsAtGC, // 1
             updatesInReadEnlistmentsAtEnlistment // 2
));

            TryAllManager.DumpPerCallSiteStats();
            }
        }

        internal void IncrementStartTryAll() {
            if (TryAllManager.ENABLE_PROFILING) {
                startTryAll++;
            }
        }

        internal void IncrementCommitSucceeded() {
            if (TryAllManager.ENABLE_PROFILING) {
                commitSucceeded++;
            }
        }

        internal unsafe void IncrementEnsureLogMemoryForUpdateLog(uint bytesNeeded) {
            if (TryAllManager.ENABLE_PROFILING) {
                ensureLogMemoryForUpdateLogCalls++;
                ensureLogMemoryForUpdateLogSlots += (bytesNeeded / (uint)sizeof(UpdateLog.Entry));
            }
        }

        internal unsafe void IncrementEnsureLogMemoryForReadEnlistmentLog(uint bytesNeeded) {
            if (TryAllManager.ENABLE_PROFILING) {
                ensureLogMemoryForReadEnlistmentLogCalls++;
                ensureLogMemoryForReadEnlistmentLogSlots += (bytesNeeded / (uint)sizeof(ReadEnlistmentLog.Entry));
            }
        }

        internal unsafe void IncrementEnsureLogMemoryForUpdateEnlistmentLog(uint bytesNeeded) {
            if (TryAllManager.ENABLE_PROFILING) {
                ensureLogMemoryForUpdateEnlistmentLogCalls++;
                ensureLogMemoryForUpdateEnlistmentLogSlots += (bytesNeeded / (uint)sizeof(UpdateEnlistmentLog.Entry));
            }
        }

        internal void IncrementLogValHeapMultiple() {
            if (TryAllManager.ENABLE_PROFILING) {
                logValHeapMultiple++;
            }
        }

        internal void IncrementLogValHeap() {
            if (TryAllManager.ENABLE_PROFILING) {
                logValHeap++;
            }
        }

        internal void IncrementLogRefHeap() {
            if (TryAllManager.ENABLE_PROFILING) {
                logRefHeap++;
            }
        }

        internal void IncrementLogIndirectValMultiple() {
            if (TryAllManager.ENABLE_PROFILING) {
                logIndirectValMultiple++;
            }
        }

        internal void IncrementLogIndirectValHeap() {
            if (TryAllManager.ENABLE_PROFILING) {
                logIndirectValHeap++;
            }
        }

        internal void IncrementLogIndirectValStack() {
            if (TryAllManager.ENABLE_PROFILING) {
                logIndirectValStack++;
            }
        }

        internal void IncrementLogIndirectRefHeap() {
            if (TryAllManager.ENABLE_PROFILING) {
                logIndirectRefHeap++;
            }
        }

        internal void IncrementLogIndirectRefStack() {
            if (TryAllManager.ENABLE_PROFILING) {
                logIndirectRefStack++;
            }
        }

        internal void IncrementSkipScan(uint n) {
            if (TryAllManager.ENABLE_PROFILING) {
                skipScan += n;
            }
        }

        internal void IncrementEnlistObjForRead() {
            if (TryAllManager.ENABLE_PROFILING) {
                enlistObjForRead++;
            }
        }

        internal void IncrementEnlistObjForUpdate() {
            if (TryAllManager.ENABLE_PROFILING) {
                enlistObjForUpdate++;
            }
        }

        internal void IncrementEnlistNewObjForUpdate() {
            if (TryAllManager.ENABLE_PROFILING) {
                enlistNewObjForUpdate++;
            }
        }

        internal void IncrementEnlistAddrForRead() {
            if (TryAllManager.ENABLE_PROFILING) {
                enlistAddrForRead++;
            }
        }

        internal void IncrementEnlistAddrForUpdate() {
            if (TryAllManager.ENABLE_PROFILING) {
                enlistAddrForUpdate++;
            }
        }

        internal void IncrementEnlistIndirectForRead() {
            if (TryAllManager.ENABLE_PROFILING) {
                enlistIndirectForRead++;
            }
        }

        internal void IncrementEnlistIndirectForUpdate() {
            if (TryAllManager.ENABLE_PROFILING) {
                enlistIndirectForUpdate++;
            }
        }

        internal void IncrementEnlistForReadLogged() {
            if (TryAllManager.ENABLE_PROFILING) {
                enlistForReadLogged++;
            }
        }

        internal void IncrementEnlistForUpdateLogged() {
            if (TryAllManager.ENABLE_PROFILING) {
                enlistForUpdateLogged++;
            }
        }

        internal void IncrementLogValHeapMultipleFast() {
            if (TryAllManager.ENABLE_PROFILING) {
                logValHeapMultipleFast++;
            }
        }

        internal void IncrementLogValHeapFast() {
            if (TryAllManager.ENABLE_PROFILING) {
                logValHeapFast++;
            }
        }

        internal void IncrementLogRefHeapFast() {
            if (TryAllManager.ENABLE_PROFILING) {
                logRefHeapFast++;
            }
        }

        internal void IncrementLogIndirectValMultipleFast() {
            if (TryAllManager.ENABLE_PROFILING) {
                logIndirectValMultipleFast++;
            }
        }

        internal void IncrementLogIndirectValHeapFast() {
            if (TryAllManager.ENABLE_PROFILING) {
                logIndirectValHeapFast++;
            }
        }

        internal void IncrementLogIndirectValStackFast() {
            if (TryAllManager.ENABLE_PROFILING) {
                logIndirectValStackFast++;
            }
        }


        internal void IncrementLogIndirectRefHeapFast() {
            if (TryAllManager.ENABLE_PROFILING) {
                logIndirectRefHeapFast++;
            }
        }

        internal void IncrementLogIndirectRefStackFast() {
            if (TryAllManager.ENABLE_PROFILING) {
                logIndirectRefStackFast++;
            }
        }

        internal void IncrementEnlistObjForReadFast() {
            if (TryAllManager.ENABLE_PROFILING) {
                enlistObjForReadFast++;
            }
        }

        internal void IncrementEnlistObjForUpdateFast() {
            if (TryAllManager.ENABLE_PROFILING) {
                enlistObjForUpdateFast++;
            }
        }

        internal void IncrementEnlistNewObjForUpdateFast() {
            if (TryAllManager.ENABLE_PROFILING) {
                enlistNewObjForUpdateFast++;
            }
        }

        internal void IncrementEnlistAddrForReadFast() {
            if (TryAllManager.ENABLE_PROFILING) {
                enlistAddrForReadFast++;
            }
        }

        internal void IncrementEnlistAddrForUpdateFast() {
            if (TryAllManager.ENABLE_PROFILING) {
                enlistAddrForUpdateFast++;
            }
        }

        internal void IncrementEnlistIndirectForReadFast() {
            if (TryAllManager.ENABLE_PROFILING) {
                enlistIndirectForReadFast++;
            }
        }

        internal void IncrementEnlistIndirectForUpdateFast() {
            if (TryAllManager.ENABLE_PROFILING) {
                enlistIndirectForUpdateFast++;
            }
        }

        internal void IncrementInvalidShake() {
            if (TryAllManager.ENABLE_PROFILING) {
                invalidShake++;
            }
        }

        internal void IncrementInvalidShakeException() {
            if (TryAllManager.ENABLE_PROFILING) {
                invalidShakeException++;
            }
        }

        internal void IncrementInvalidConflict() {
            if (TryAllManager.ENABLE_PROFILING) {
                invalidConflict++;
            }
        }

        internal void IncrementInvalidRace() {
            if (TryAllManager.ENABLE_PROFILING) {
                invalidRace++;
            }
        }

        internal void IncrementInvalidDuringGC() {
            if (TryAllManager.ENABLE_PROFILING) {
                invalidDuringGC++;
            }
        }

        internal void IncrementInvalidOutsideGC() {
            if (TryAllManager.ENABLE_PROFILING) {
                invalidOutsideGC++;
            }
        }

        internal void IncrementEnlistmentOverflow() {
            if (TryAllManager.ENABLE_PROFILING) {
                enlistmentOverflow++;
            }
        }

        internal void IncrementInflationSeen() {
            if (TryAllManager.ENABLE_PROFILING) {
                inflationSeen++;
            }
        }

        internal void IncrementUpdateOverflow() {
            if (TryAllManager.ENABLE_PROFILING) {
                updateOverflow++;
            }
        }

        internal void IncrementUpdateLogged(UpdateLog.EntryKind kind) {
            if (TryAllManager.ENABLE_PROFILING) {
                switch (kind) {
                case UpdateLog.EntryKind.HEAP_VAL:
                    this.loggedHeapVal++;
                    break;
                    
                case UpdateLog.EntryKind.HEAP_REF:
                    this.loggedHeapRef++;
                    break;
                    
                case UpdateLog.EntryKind.NON_HEAP_VAL:
                    this.loggedNonHeapVal++;
                    break;
                    
                case UpdateLog.EntryKind.NON_HEAP_REF:
                    this.loggedNonHeapRef++;
                    break;
                    
                default:
                    VTable.Assert(false);
                    break;
                }
            }
        }

        internal void IncrementLocalUpdate(UpdateLog.EntryKind kind) {
            if (TryAllManager.ENABLE_PROFILING) {
                switch (kind) {
                case UpdateLog.EntryKind.HEAP_VAL:
                    this.localUpdateHeapVal++;
                    break;
                    
                case UpdateLog.EntryKind.HEAP_REF:
                    this.localUpdateHeapRef++;
                    break;
                    
                case UpdateLog.EntryKind.NON_HEAP_VAL:
                    this.localUpdateNonHeapVal++;
                    break;
                    
                case UpdateLog.EntryKind.NON_HEAP_REF:
                    this.localUpdateNonHeapRef++;
                    break;
                    
                default:
                    VTable.Assert(false);
                    break;
                }
            }
        }

        internal void IncrementUpdateHitInCache(UpdateLog.EntryKind kind) {
            if (TryAllManager.ENABLE_PROFILING) {
                switch (kind) {
                case UpdateLog.EntryKind.HEAP_VAL:
                    this.updateHitInCacheHeapVal++;
                    break;
                    
                case UpdateLog.EntryKind.HEAP_REF:
                    this.updateHitInCacheHeapRef++;
                    break;
                    
                case UpdateLog.EntryKind.NON_HEAP_VAL:
                    this.updateHitInCacheNonHeapVal++;
                    break;
                    
                case UpdateLog.EntryKind.NON_HEAP_REF:
                    this.updateHitInCacheNonHeapRef++;
                    break;
                
                default:
                    VTable.Assert(false);
                    break;
                }
            }
        }

        internal void IncrementUpdateHitInBitmap(UpdateLog.EntryKind kind) {
            if (TryAllManager.ENABLE_PROFILING) {
                switch (kind) {
                case UpdateLog.EntryKind.HEAP_VAL:
                    this.updateHitInBitmapHeapVal++;
                    break;
                    
                case UpdateLog.EntryKind.HEAP_REF:
                    this.updateHitInBitmapHeapRef++;
                    break;
                    
                case UpdateLog.EntryKind.NON_HEAP_VAL:
                    this.updateHitInBitmapNonHeapVal++;
                    break;
                    
                case UpdateLog.EntryKind.NON_HEAP_REF:
                    this.updateHitInBitmapNonHeapRef++;
                    break;
                    
                default:
                    VTable.Assert(false);
                    break;
                }
            }
        }

        internal void IncrementCachesCreated() {
            if (TryAllManager.ENABLE_PROFILING) {
                cachesCreated++;
            }
        }

        internal void IncrementReadsHitInCache() {
            if (TryAllManager.ENABLE_PROFILING) {
                readsHitInCache++;
            }
        }

        internal void IncrementBitmapOverflows() {
            if (TryAllManager.ENABLE_PROFILING) {
                bitmapOverflows++;
            }
        }

        internal void IncrementExternalBitmaps() {
            if (TryAllManager.ENABLE_PROFILING) {
                externalBitmaps++;
            }
        }

        internal void IncrementForcedGC() {
            if (TryAllManager.ENABLE_PROFILING) {
                forcedGC++;
            }
        }

        internal void IncrementWeakRefsClearedInReadEnlistmentLog() {
            if (TryAllManager.ENABLE_PROFILING) {
                weakRefsClearedInReadEnlistmentLog++;
            }
        }

        internal void IncrementWeakRefsClearedInUpdateEnlistmentLog() {
            if (TryAllManager.ENABLE_PROFILING) {
                weakRefsClearedInUpdateEnlistmentLog++;
            }
        }

        internal void IncrementWeakRefsClearedInUpdateLog() {
            if (TryAllManager.ENABLE_PROFILING) {
                weakRefsClearedInUpdateLog++;
            }
        }

        internal void IncrementReadDuplicatesRemoved() {
            if (TryAllManager.ENABLE_PROFILING) {
                readDuplicatesRemoved++;
            }
        }

        internal void IncrementUpdatesInReadEnlistmentsAtGC() {
            if (TryAllManager.ENABLE_PROFILING) {
                updatesInReadEnlistmentsAtGC++;
            }
        }

        internal void IncrementUpdatesInReadEnlistmentsAtEnlistment() {
            if (TryAllManager.ENABLE_PROFILING) {
                updatesInReadEnlistmentsAtEnlistment++;
            }
        }

        internal uint startTryAll;
        internal uint commitSucceeded;
        internal uint ensureLogMemoryForUpdateEnlistmentLogCalls;
        internal uint ensureLogMemoryForUpdateEnlistmentLogSlots;
        internal uint ensureLogMemoryForReadEnlistmentLogCalls;
        internal uint ensureLogMemoryForReadEnlistmentLogSlots;
        internal uint ensureLogMemoryForUpdateLogCalls;
        internal uint ensureLogMemoryForUpdateLogSlots;
        internal uint logValHeapMultiple;
        internal uint logValHeap;
        internal uint logRefHeap;
        internal uint logIndirectValMultiple;
        internal uint logIndirectValHeap;
        internal uint logIndirectValStack;
        internal uint logIndirectRefHeap;
        internal uint logIndirectRefStack;
        internal uint logValHeapMultipleFast;
        internal uint logValHeapFast;
        internal uint logRefHeapFast;
        internal uint logIndirectValMultipleFast;
        internal uint logIndirectValHeapFast;
        internal uint logIndirectValStackFast;
        internal uint logIndirectRefHeapFast;
        internal uint logIndirectRefStackFast;
        internal uint skipScan;
        internal uint enlistObjForRead;
        internal uint enlistObjForUpdate;
        internal uint enlistNewObjForUpdate;
        internal uint enlistAddrForRead;
        internal uint enlistAddrForUpdate;
        internal uint enlistIndirectForRead;
        internal uint enlistIndirectForUpdate;
        internal uint enlistForReadLogged;
        internal uint enlistForUpdateLogged;
        internal uint enlistObjForReadFast;
        internal uint enlistObjForUpdateFast;
        internal uint enlistNewObjForUpdateFast;
        internal uint enlistAddrForReadFast;
        internal uint enlistAddrForUpdateFast;
        internal uint enlistIndirectForReadFast;
        internal uint enlistIndirectForUpdateFast;
        internal uint invalidShake;
        internal uint invalidShakeException;
        internal uint invalidConflict;
        internal uint invalidRace;
        internal uint invalidDuringGC;
        internal uint invalidOutsideGC;
        internal uint inflationSeen;
        internal uint updateOverflow;
        internal uint enlistmentOverflow;
        internal uint loggedHeapVal;
        internal uint loggedHeapRef;
        internal uint loggedNonHeapVal;
        internal uint loggedNonHeapRef;
        internal uint readsHitInCache;
        internal uint updateHitInCacheHeapVal;
        internal uint updateHitInCacheHeapRef;
        internal uint updateHitInCacheNonHeapVal;
        internal uint updateHitInCacheNonHeapRef;
        internal uint updateHitInBitmapHeapVal;
        internal uint updateHitInBitmapHeapRef;
        internal uint updateHitInBitmapNonHeapVal;
        internal uint updateHitInBitmapNonHeapRef;
        internal uint localUpdateHeapVal;
        internal uint localUpdateHeapRef;
        internal uint localUpdateNonHeapVal;
        internal uint localUpdateNonHeapRef;
        internal uint updatesInReadEnlistmentsAtGC;
        internal uint updatesInReadEnlistmentsAtEnlistment;
        internal uint cachesCreated;
        internal uint bitmapOverflows;
        internal uint externalBitmaps;
        internal uint forcedGC;
        internal uint weakRefsClearedInReadEnlistmentLog;
        internal uint weakRefsClearedInUpdateEnlistmentLog;
        internal uint weakRefsClearedInUpdateLog;
        internal uint readDuplicatesRemoved;

        internal TryAllCounters next;
    }

}
