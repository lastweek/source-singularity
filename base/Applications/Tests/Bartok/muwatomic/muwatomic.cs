//
// Copyright (c) Microsoft Corporation.   All rights reserved.
//

namespace AtomicTest
{
  using System;

  internal class Test : Object {
      internal int x;
  }

  public class muw {

      public volatile static Object o2;
      public volatile static Object o3;

      public static void Main(String[] args) {
          bool forceGC = true;

          foreach (String arg in args) {
              if (arg.Equals("nogc")) {
                  forceGC = false;
              }
          }

          for (int i = 0; i < 10; i ++) {
              Test lo1 = new Test();
              Test lo2 = new Test();
              Test lo3 = new Test();
              Test lo4 = new Test();
              Test lock_only = new Test();
              int h;

              int h_in1 = 0;
              int h_in2 = 0;
              int v = 0;

              h = lo3.GetHashCode();
              h = lo4.GetHashCode();
          
              // Read from non-inflated objects
              Console.WriteLine("\n\nReading in an atomic block");
              try {
                  v = lo1.x;
                  v = lo2.x;
                  if (forceGC) {
                      GC.Collect();
                  }
              }
              catch (AtomicFakeException) {
              }

              // Read-modify-write non-inflated objects
              Console.WriteLine("\n\nRead-modify-write in an atomic block");
              try {
                  lo1.x ++;
                  lo2.x ++;
                  if (forceGC) {
                      GC.Collect();
                  }
              }
              catch (AtomicFakeException) {
              }

              // Read from objects whose multi-use-word is in use
              Console.WriteLine("\n\nRead from object with multi-use-word in use");
              try {
                  v = lo3.x;
                  v = lo4.x;
                  if (forceGC) {
                      GC.Collect();
                  }
              }
              catch (AtomicFakeException) {
              }

              // Read-modify-write objects whose multi-use-word is in use
              Console.WriteLine("\n\nRead-modify-write from object with multi-use-word in use");
              try {
                  lo3.x ++;
                  lo4.x ++;
                  if (forceGC) {
                      GC.Collect();
                  }
              }
              catch (AtomicFakeException) {
              }

              // Trigger inflation within a read-modify-write atomic block
              Console.WriteLine("\n\nTrigger inflation in a read-modify-write atomic block");
              try {
                  lo1.x ++;
                  h_in1 = lo1.GetHashCode();
                  if (forceGC) {
                      GC.Collect();
                  }
              }
              catch (AtomicFakeException) {
              }

              // Trigger inflation within a read-only atomic block
              Console.WriteLine("\n\nTrigger inflation in a read-only atomic block");
              try {
                  v = lo2.x;
                  h_in2 = lo2.GetHashCode();
                  if (forceGC) {
                      GC.Collect();
                  }
              }
              catch (AtomicFakeException) {
              }

              // Read an inflated object
              Console.WriteLine("\n\nReading from an inflated object in an atomic block");
              try {
                  v = lo1.x;
                  v = lo2.x;
                  if (forceGC) {
                      GC.Collect();
                  }
              }
              catch (AtomicFakeException) {
              }

              // Read-modify-write an inflated object
              Console.WriteLine("\n\nRead-modify-write an inflated object in an atomic block");
              try {
                  v = lo1.x++;
                  v = lo2.x++;
                  if (forceGC) {
                      GC.Collect();
                  }
              }
              catch (AtomicFakeException) {
              }
          
              // Read-modify-write an inflated object
              Console.WriteLine("\n\nRead-modify-write an inflated object in an atomic block");
              try {
                  v = lo1.x++;
                  v = lo2.x++;
                  if (forceGC) {
                      GC.Collect();
                  }
              }
              catch (AtomicFakeException) {
              }

              h = lo1.GetHashCode();
              Console.WriteLine("\n\nDiff on lo1.GetHashCode() = " + (h-h_in1));
              h = lo2.GetHashCode();
              Console.WriteLine("Diff on lo2.GetHashCode() = " + (h-h_in2));
          }
      }
  }
}
