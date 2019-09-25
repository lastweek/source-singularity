//
// Copyright (c) Microsoft Corporation.   All rights reserved.
//

/*******************************************************************/
/*                           WARNING                               */
/* This file should be identical in the Bartok and Singularity     */
/* depots. Master copy resides in Bartok Depot. Changes should be  */
/* made to Bartok Depot and propagated to Singularity Depot.       */
/*******************************************************************/

namespace System.GCs {

  internal class Trace {
      [Flags]
      internal enum Area {
          Pointer  = 0x01,
          Page     = 0x02,
          Heap     = 0x04,
          Stack    = 0x08,
          Thread   = 0x10,
          Allocate = 0x20,
          Emu      = 0x40
      }

      internal static Area filterArea = 0;

      internal static UIntPtr filter;
      internal static UIntPtr filterLow;
      internal static UIntPtr filterHigh;

      [System.Diagnostics.Conditional("TRACE")]
      internal static void Log(Area area, String v, __arglist) {
          if ((area & Trace.filterArea) == 0) {
              return;
          }

          bool tryFind = false;
          bool found = false;
          if (filter != UIntPtr.Zero) {
              tryFind = true;
              ArgIterator argsFilter = new ArgIterator(__arglist);

              while (argsFilter.GetRemainingCount() > 0) {
                  TypedReference tr = argsFilter.GetNextArg();
                  Type t = __reftype(tr);
                  if (t == typeof(System.UIntPtr)) {
                      UIntPtr u = __refvalue(tr, UIntPtr);
                      if (u == filter) {
                          found = true;
                          break;
                      }
                  }
              }
          }

          if (!found && (filterLow != UIntPtr.Zero)) {
              tryFind = true;
              ArgIterator argsFilter = new ArgIterator(__arglist);

              while (argsFilter.GetRemainingCount() > 0) {
                  TypedReference tr = argsFilter.GetNextArg();
                  Type t = __reftype(tr);
                  if (t == typeof(System.UIntPtr)) {
                      UIntPtr u = __refvalue(tr, UIntPtr);
                      if ((u >= filterLow) && (u <= filterHigh)) {
                          found = true;
                          break;
                      }
                  }
              }
          }

          if (tryFind && !found) {
             return;
          }

          ArgIterator args = new ArgIterator(__arglist);
          VTable.DebugPrint(v, args);
          VTable.DebugPrint("\n");
      }
  }
}
