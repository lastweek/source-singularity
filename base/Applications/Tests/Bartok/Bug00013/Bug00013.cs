//
// Copyright (c) Microsoft Corporation.   All rights reserved.
//

// Some sort of threads/locking test.
// See usage for parameter.
// DebubPrintSpinLock was in the Marmot runtime.

using System;
using System.Threading;
using Microsoft.Contracts;
using Microsoft.SingSharp.Reflection;
using Microsoft.Singularity.Channels;
using Microsoft.Singularity.Applications;
using Microsoft.Singularity.Io;
using Microsoft.Singularity.Configuration;
[assembly: Transform(typeof(ApplicationResourceTransform))]

namespace MarmotBugs
{
    [ConsoleCategory(HelpMessage="Show attributes associated with a file", DefaultAction=true)]
    internal class Parameters {
    
        [InputEndpoint("data")]
        public readonly TRef<UnicodePipeContract.Exp:READY> Stdin;

        [OutputEndpoint("data")]
        public readonly TRef<UnicodePipeContract.Imp:READY> Stdout;

        [LongParameter( "t", Default=1,  HelpMessage="threads")]
        internal long threads;

        reflective internal Parameters();

        internal int AppMain() {
            Bug00013.AppMain(this);
            return 0;
        }
    }

  class DebugPrintSpin
  {
      private static Object locker = new Object();
      public static void Lock() {
          //    Class_java_lang_Thread *currentThread = CurrentThread();
          //    currentThread->f_isAwaitingDebugPrintSpinLock = true;
          System.Threading.Monitor.Enter(locker);
          //    DebugPrintCriticalSectionHolder = currentThread;
          //    currentThread->f_isAwaitingDebugPrintSpinLock = false;
      }
      public static void Unlock() {
          //    DebugPrintCriticalSectionHolder = NULL;
          System.Threading.Monitor.Exit(locker);
      }
  }

  class Bug00013
  { //: Runnable {

      static int totalThreads = Int32.MaxValue;

      const bool    wasteSpace  = true;
      const bool    showPended  = false;

      const int        maxLinks    =   10;
      const int        maxThreads  =   10;
      const int        maxActive   =    4;
      const int        nodeTraverse=   50;
      const int        linkTraverse=  500;

      const int        newThreads  =    2; //10;
      const int        newNodes    =  100;
      const int        newLinks    =  700;
      const int        newRejects  = 1000;

      // conversion filler
      public static void DebugDumpThreadAnchorTable(int i) {}
      private static void DebugBreak() {
          Assert(false, "DebugBreak");
      }
      private static void Assert(bool b) {
          Assert(b, "Assertion failed");
      }
      private static void Assert(bool b, String s) {
          if (!b) {
              DebugPrintSpin.Lock();
              Console.WriteLine(s);
              Console.WriteLine("Failed Bug00013");
              DebugPrintSpin.Unlock();
              Environment.Exit(1);
          }
      }
      // end conversion

      void nonsyncv() {
      lock (this) {
          DebugPrintSpin.Lock();
          Console.WriteLine("within nonsyncv()");
          DebugDumpThreadAnchorTable(4);
          DebugPrintSpin.Unlock();
      }
      }

      [System.Runtime.CompilerServices.MethodImpl
      (System.Runtime.CompilerServices.MethodImplOptions.Synchronized)]
      void syncv() {
          DebugPrintSpin.Lock();
          Console.WriteLine("within syncv()");
          DebugDumpThreadAnchorTable(4);
          DebugPrintSpin.Unlock();
      }

      static void nonsyncs() {
      lock (ClassBug00013) {
          DebugPrintSpin.Lock();
          Console.WriteLine("within nonsyncs()");
          DebugDumpThreadAnchorTable(4);
          DebugPrintSpin.Unlock();
      }
      }

      [System.Runtime.CompilerServices.MethodImpl
      (System.Runtime.CompilerServices.MethodImplOptions.Synchronized)]
      static void syncs() {
          DebugPrintSpin.Lock();
          Console.WriteLine("within syncs()");
          DebugDumpThreadAnchorTable(4);
          DebugPrintSpin.Unlock();
      }

      static void usage() {
          Console.WriteLine("usage:  Bug00013 [total_threads]");
          Environment.Exit(1);
      }

      internal static void AppMain(Parameters! config) 
      {
          totalThreads = (int)config.threads;

          undeadThreadids = new int[2*maxThreads];

          DebugPrintSpin.Lock();
          Console.WriteLine("Bug00013.Main()");
          DebugDumpThreadAnchorTable(4);
          DebugPrintSpin.Unlock();

          Object Lock = new Object();
          Bug00013.Lock = Lock;
          DebugPrintSpin.Lock();
          Console.Write("Bug00013.Lock = ");
          Console.WriteLine(Lock.GetHashCode());
          DebugPrintSpin.Unlock();

          anchor = new Bug00013();
          DebugPrintSpin.Lock();
          Console.Write("Bug00013.Type = ");
          Console.WriteLine(anchor.GetType());
          DebugPrintSpin.Unlock();

          ClassBug00013 = anchor.GetType();
          DebugPrintSpin.Lock();
          Console.Write("Bug00013.class = ");
          Console.WriteLine(ClassBug00013.GetHashCode());
          DebugPrintSpin.Unlock();

          bug13Type = anchor.GetType();
          linksType = anchor.links.GetType();

          //==================================================================

          DebugPrintSpin.Lock();
          Console.WriteLine();
          Console.WriteLine("//======================================" +
                                  "=======================================");
          Console.WriteLine();
          Console.WriteLine("before nonsyncv()");
          DebugPrintSpin.Unlock();

          anchor.nonsyncv();

          DebugPrintSpin.Lock();
          Console.WriteLine("after  nonsyncv()");
          DebugPrintSpin.Unlock();

          //==================================================================

          DebugPrintSpin.Lock();
          Console.WriteLine();
          Console.WriteLine("//======================================" +
                                  "=======================================");
          Console.WriteLine();
          Console.WriteLine("before syncv()");
          DebugPrintSpin.Unlock();

          anchor.syncv();

          DebugPrintSpin.Lock();
          Console.WriteLine("after  syncv()");
          DebugPrintSpin.Unlock();

          //==================================================================

          DebugPrintSpin.Lock();
          Console.WriteLine();
          Console.WriteLine("//======================================" +
                                  "=======================================");
          Console.WriteLine();
          Console.WriteLine("before nonsyncs()");
          DebugPrintSpin.Unlock();

          nonsyncs();

          DebugPrintSpin.Lock();
          Console.WriteLine("after  nonsyncs()");
          DebugPrintSpin.Unlock();

          //==================================================================

          DebugPrintSpin.Lock();
          Console.WriteLine();
          Console.WriteLine("//======================================" +
                                  "=======================================");
          Console.WriteLine();
          Console.WriteLine("before syncs()");
          DebugPrintSpin.Unlock();

          syncs();

          DebugPrintSpin.Lock();
          Console.WriteLine("after  syncs()");
          DebugPrintSpin.Unlock();

          //==================================================================

          Thread newThread = new Thread(new ThreadStart(anchor.run));
          DebugPrintSpin.Lock();
          Console.WriteLine();
          Console.WriteLine("//======================================" +
                                  "=======================================");
          Console.WriteLine();
          Console.Write("newThread = ");
          Console.WriteLine(newThread.GetHashCode());
          DebugPrintSpin.Unlock();

          //
          //new WatchDog().start();
          //try {
          //  Thread.sleep(1000);
          //}
          //catch (InterruptedException e) {
          //}
          ///*  

          newThread.Start();

          deadman = System.DateTime.Now;
          for (;;) {
              //try {
                  Thread.Sleep(25000);
                  //} catch(ThreadInterruptedException) {
                  //DebugPrintSpin.Lock();
                  //Console.WriteLine("!");
                  //DebugPrintSpin.Unlock();
                  // }
              lock (Lock) {
                  DebugPrintSpin.Lock();
                  long deadms = (System.DateTime.Now - deadman).Milliseconds;
                  if (deadms > 100000) {
                      Console.WriteLine();
                      Console.WriteLine("Bug00013.Main()"
                                              + "  deadman expired");
                      DebugDumpThreadAnchorTable(4);
                      DebugBreak();
                  }
                  else {
                      Console.WriteLine();
                      Console.Write(" ?<0,");
                      Console.Write(numThreadsAlive);
                      Console.Write(",");
                      Console.Write(numThreadsActive);
                      DebugPrintUndead();
                      Console.Write("> ");
                  }
                  DebugPrintSpin.Unlock();
                  if (numThreadsAlive == 0) break;
              }
          }
          Console.WriteLine("Passed Bug00013");
      }

      Bug00013() {
          lock (Lock) {
              nodeid = nodeidGenerator++;
          }
          nodename = ("Node" + nodeid);
          links = new Bug00013[maxLinks];
      }

      //
      //public override String ToString() {
      //  if (nodename != null) return(nodename);
      //  return(base.ToString());
      //}
      //

      public void run() {
          int myNumThreadsAlive;
          int myNumThreadsActive;
          lock (Lock) {
              Assert(numThreadsAlive >= 0,
                     "run()  numThreadsAlive should be >= 0");
              Assert(numThreadsActive >= 0,
                     "run()  numThreadsActive should be >= 0");
              numThreadsAlive++;
              myNumThreadsAlive = numThreadsAlive;
              numThreadsActive++;
              myNumThreadsActive = numThreadsActive;
              threadid = ++threadidGenerator;
              recordUndead();
          }
          DebugPrintSpin.Lock();
          Console.WriteLine();
          Console.Write("T+<");
          Console.Write(threadid);
          Console.Write(",");
          Console.Write(myNumThreadsAlive);
          Console.Write(",");
          Console.Write(myNumThreadsActive);
          Console.Write("> ");
          DebugPrintSpin.Unlock();
          if ((myNumThreadsAlive <= maxThreads)
               && (threadid < totalThreads)) {
              bool conflict = false;
              lock (this) {
                  if (random == null) {
                      random = new Random();
                  }
                  else {
                      conflict = true;
                  }
              }
              if (!conflict) {
                  traversalLimit = nodeTraverse;
                  Bug00013 last = this;
                  Bug00013 next = this;
                  Bug00013 node = new Bug00013();
                  anchor.addLink(this, node);

                  for (int i = 0; i < newThreads; i++) {
                      traversalLimit = nodeTraverse;
                      int strides = 0;
                      for (int j = 0; j < newNodes; j++) {
                          recordUndead();
                          node = new Bug00013();
                          if (wasteSpace) {
                              while (newNodes
                                     < newRejects*random.NextDouble()) {
                                  Object ooo = new int[1057];
                                  node = new Bug00013();
                              }
                          }
                          strides = 100 + (int)(1000*random.NextDouble());
                          last = traverse(last, strides);
                          while (!addLink(last, node)) {
                              strides = 100 + (int)(1000*random.NextDouble());
                              last = traverse(last, strides);
                          }
                          strides = 100 + (int)(1000*random.NextDouble());
                          next = traverse(next, strides);
                          while (!addLink(next, node)) {
                              strides = 100 + (int)(1000*random.NextDouble());
                              next = traverse(next, strides);
                          }
                      }
                      DebugPrintSpin.Lock();
                      Console.Write("n");
                      Console.Write(threadid);
                      DebugPrintSpin.Unlock();
                      traversalLimit = linkTraverse;
                      for (int j = 4*newNodes; j < newLinks; j += 2) {
                          last = traverse(last, strides);
                          next = traverse(next, strides);
                          while (!addLink(last, next)) {
                              strides = 100 + (int)(1000*random.NextDouble());
                              last = traverse(last, strides);
                              strides = 100 + (int)(1000*random.NextDouble());
                              next = traverse(next, strides);
                          }
                      }
                      DebugPrintSpin.Lock();
                      Console.Write("l");
                      Console.Write(threadid);
                      DebugPrintSpin.Unlock();

                      Thread newThread = new Thread(new ThreadStart(last.run));
                      DebugPrintSpin.Lock();
                      Console.Write("t");
                      Console.Write(threadid);
                      DebugPrintSpin.Unlock();
                      newThread.Start();
                  }
              }
          }
          lock (Lock) {
              recordUndead();
              Assert(numThreadsAlive > 0,
                     "run()  numThreadsAlive should be > 0");
              Assert(numThreadsActive > 0,
                     "run()  numThreadsActive should be > 0");
              numThreadsAlive--;
              myNumThreadsAlive = numThreadsAlive;
              numThreadsActive--;
              myNumThreadsActive = numThreadsActive;
          }
          DebugPrintSpin.Lock();
          Console.WriteLine();
          Console.Write("T-<");
          Console.Write(threadid);
          Console.Write(",");
          Console.Write(myNumThreadsAlive);
          Console.Write(",");
          Console.Write(myNumThreadsActive);
          Console.Write("> ");
          DebugPrintSpin.Unlock();
          notifyPending();
      }

      Bug00013 traverse(Bug00013 node, int numStrides) {
          lock (Lock) {
              recordUndead();
          }
          for (int i = 0; i < numStrides; i++) {
              Assert(traversalsLeft >= 0);
              if (traversalsLeft > traversalLimit) {
                  traversalsLeft = traversalLimit;
              }
              if (traversalsLeft == 0) {
                  bool pended = false;
                  int myNumThreadsAlive;
                  int myNumThreadsActive;
                  lock (Lock) {
                      Assert(numThreadsActive > 0);
                      Assert(nextPending == null);
                      if ((numThreadsActive > maxActive)
                          || (pendingQueue != null)) {
                          pended = showPended;
                          isPending = true;
                          if (pendingQueue != null) {
                              Bug00013 pend = pendingQueue;
                              for (;;) {
                                  Bug00013 curr = pend;
                                  pend = curr.nextPending;
                                  if (pend == null) {
                                      curr.nextPending = this;
                                      break;
                                  }
                              }
                          }
                          else {
                              pendingQueue = this;
                          }
                      }
                      numThreadsActive--;
                      myNumThreadsAlive = numThreadsAlive;
                      myNumThreadsActive = numThreadsActive;
                  }
                  if (pended) {
                      DebugPrintSpin.Lock();
                      Console.WriteLine();
                      Console.Write("T_<");
                      Console.Write(threadid);
                      Console.Write(",");
                      Console.Write(myNumThreadsAlive);
                      Console.Write(",");
                      Console.Write(myNumThreadsActive);
                      Console.Write("> ");
                      DebugPrintSpin.Unlock();
                  }
                  notifyPending();
                  lock (this) {
                      while (isPending) {
                          //try {
                              Monitor.Wait(this);
                              //} catch(ThreadInterruptedException) {}
                      }
                      Assert(nextPending == null);
                  }
                  lock (Lock) {
                      Assert(numThreadsAlive > 0,
                             "run()  numThreadsAlive should be > 0");
                      Assert(numThreadsActive >= 0,
                             "run()  numThreadsActive should be >= 0");
                      myNumThreadsAlive = numThreadsAlive;
                      numThreadsActive++;
                      myNumThreadsActive = numThreadsActive;
                      recordUndead();
                  }
                  if (pended) {
                      DebugPrintSpin.Lock();
                      Console.WriteLine();
                      Console.Write("T=<");
                      Console.Write(threadid);
                      Console.Write(",");
                      Console.Write(myNumThreadsAlive);
                      Console.Write(",");
                      Console.Write(myNumThreadsActive);
                      Console.Write("< ");
                      DebugPrintSpin.Unlock();
                  }
                  traversalsLeft = traversalLimit;
              }
              traversalsLeft--;
              lock (node) {
                  if (node.numLinks > 0) {
                      int link = (int)(node.numLinks*random.NextDouble());
                      Assert(link >= 0,
                             "traverse()  selected link should be nonnegative");
                      Assert(link < node.numLinks,
                             "traverse()  selected link should be < numLinks");
                      if (node.links[link] == null) {
                          DebugPrintSpin.Lock();
                          Console.WriteLine("BUG at link "+link);
                          for (int ii = 0; ii < node.numLinks; ii++) {
                              Console.WriteLine("link["+ii+"] is "
                                                      +node.links[ii]);
                          }
                          Console.WriteLine("link["+link+"] is "
                                                  +node.links[link]);
                          DebugPrintSpin.Unlock();
                      }
                      Assert(node.links[link] != null,
                             "traverse()  selected link should not be null");
                      node = node.links[link];
                  }
              }
          }
          return(node);
      }

      bool addLink(Bug00013 last, Bug00013 next) {
          Assert(last != null, "addlink()  last should not be null");
          Assert(next != null, "addlink()  next should not be null");
          if (last == next) return(false);
          bool lastLinked = false;
          int lastLinks;
          bool nextLinked = false;
          int nextLinks;
          lock (last) {
              checkConsistency();
              if (last.numLinks < maxLinks) {
                  lastLinked = true;
                  for (int i = 0; i < last.numLinks; i++) {
                      if (last.links[i] == next) {
                          lastLinked = false;
                          break;
                      }
                  }
                  if (lastLinked) {
                      last.links[last.numLinks++] = next;
                      lastLinks = last.numLinks;
                  }
              }
              checkConsistency();
          }
          if (!lastLinked) {
              //  last can't take another link
              //  or these two nodes are already linked
              return(false);
          }
          lock (next) {
              checkConsistency();
              if (next.numLinks < maxLinks) {
                  nextLinked = true;
                  for (int i = 0; i < next.numLinks; i++) {
                      Assert(next.links[i] != last,
                             "addlink()  should not already be linked to last");
                  }
                  next.links[next.numLinks++] = last;
                  nextLinks = next.numLinks;
              }
              checkConsistency();
          }
          if (nextLinked) {
              return(true);
          }
          lock (last) {
              checkConsistency();
              Assert(last.numLinks>0, "addlink()  last.numLinks should be > 0");
              last.numLinks--;
              for (int i = 0; i < last.numLinks; i++) {
                  if (last.links[i] == next) {
                      last.links[i] = last.links[last.numLinks];
                      break;
                  }
              }
              last.links[last.numLinks] = null;
              checkConsistency();
          }
          return(false);
      }

      void notifyPending() {
          lock (Lock) {
              Bug00013 firstPending = pendingQueue;
              if ((firstPending != null) && (numThreadsActive < maxActive)) {
                  pendingQueue = firstPending.nextPending;
                  firstPending.nextPending = null;
                  lock (firstPending) {
                      firstPending.isPending = false;
                      Monitor.PulseAll(firstPending);
                  }
              }
          }
      }

      void recordUndead() {
          if (threadid == 0) DebugBreak();
          deadman = System.DateTime.Now;
          for (int i = 0; i < numUndeadThreadids; i++) {
              if (undeadThreadids[i] == threadid) {
                  return;
              }
              if (undeadThreadids[i] > threadid) {
                  if (numUndeadThreadids == undeadThreadids.Length) {
                      numUndeadThreadids--;
                  }
                  for (int j = numUndeadThreadids; j > i; j--) {
                      undeadThreadids[j] = undeadThreadids[j-1];
                  }
                  undeadThreadids[i] = threadid;
                  numUndeadThreadids++;
                  return;
              }
          }
          if (numUndeadThreadids == undeadThreadids.Length) return;
          undeadThreadids[numUndeadThreadids++] = threadid;
      }

      static void DebugPrintUndead() {
          char sep = ':';
          for (int i = 0; i < numUndeadThreadids; i++) {
              Console.Write(sep);
              Console.Write(undeadThreadids[i]);
              sep = ',';
          }
          numUndeadThreadids = 0;
      }

      private void checkConsistency() {
          bool locked = false;
          if (this.GetType() != bug13Type) {
              if (!locked) {
                  DebugPrintSpin.Lock();
                  Console.WriteLine();
                  Console.Write("Bug00013 ");
                  Console.Write(this);
                  Console.WriteLine(":");
                  locked = true;
              }
              Console.Write("    vtable ");
              Console.Write(this.GetType());
              Console.Write(" s/b ");
              Console.Write(bug13Type);
              Console.WriteLine();
          }
          if (links.GetType() != linksType) {
              if (!locked) {
                  DebugPrintSpin.Lock();
                  Console.WriteLine();
                  Console.Write("Bug00013 ");
                  Console.Write(this);
                  Console.WriteLine(":");
                  locked = true;
              }
              Console.Write("    links.vtable ");
              Console.Write(links.GetType());
              Console.Write(" s/b ");
              Console.Write(linksType);
              Console.WriteLine();
          }
          if (links.Length != maxLinks) {
              if (!locked) {
                  DebugPrintSpin.Lock();
                  Console.WriteLine();
                  Console.Write("Bug00013 ");
                  Console.Write(this);
                  Console.WriteLine(":");
                  locked = true;
              }
              Console.Write("    links.Length ");
              Console.Write(links.Length);
              Console.Write(" s/b ");
              Console.Write(maxLinks);
              Console.WriteLine();
          }
          for (int i = 0; i < links.Length; i++) {
              if (links[i] == null) continue;
              if (links[i].GetType() != bug13Type) {
                  if (!locked) {
                      DebugPrintSpin.Lock();
                      Console.WriteLine();
                      Console.Write("Bug00013 ");
                      Console.Write(this);
                      Console.WriteLine(":");
                      locked = true;
                  }
                  Console.Write("    links[");
                  Console.Write(i);
                  Console.Write("].vtable ");
                  Console.Write(this.GetType());
                  Console.Write(" s/b ");
                  Console.Write(bug13Type);
                  Console.WriteLine();
              }
          }
          if (locked) {
              DebugBreak();
              DebugPrintSpin.Unlock();
          }
      }

      //  node fields

      int                     nodeid;
      String                  nodename;
      int                     numLinks;
      Bug00013[]              links;

      //  thread/runnable fields

      int                     threadid;
      Random                  random;
      int                     traversalLimit;
      int                     traversalsLeft;
      bool                 isPending;
      Bug00013                nextPending;

      //  global/statics

      static Bug00013         anchor;

      static Object           Lock;
      static int              nodeidGenerator;
      static int              threadidGenerator;
      static int              numThreadsAlive;
      static int              numThreadsActive;
      static DateTime         deadman;
      static Type             ClassBug00013;
      static Bug00013         pendingQueue;
      static int              numUndeadThreadids;
      static int[]            undeadThreadids;

      static Type             bug13Type;
      static Type             linksType;
  }

  class WatchDog
  { // : Thread {
      WatchDog() {} //: base("WatchDog") {}

      public void run() {
          DebugPrintSpin.Lock();
          Console.WriteLine("WatchDog sleeping");
          DebugPrintSpin.Unlock();
          //try {
              Thread.Sleep(200000);
              //} catch(ThreadInterruptedException) {
              //DebugPrintSpin.Lock();
              //Console.WriteLine("!");
              //DebugPrintSpin.Unlock();
              //}
          DebugPrintSpin.Lock();
          Console.WriteLine("WatchDog awake");
          Bug00013.DebugDumpThreadAnchorTable(4);
          Console.WriteLine("WatchDog exitting");
          DebugPrintSpin.Unlock();
      }
  }
}
