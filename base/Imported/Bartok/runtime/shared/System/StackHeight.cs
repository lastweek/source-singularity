//
// Copyright (c) Microsoft Corporation.   All rights reserved.
//

/*******************************************************************/
/*                           WARNING                               */
/* This file should be identical in the Bartok and Singularity     */
/* depots. Master copy resides in Bartok Depot. Changes should be  */
/* made to Bartok Depot and propagated to Singularity Depot.       */
/*******************************************************************/


namespace System {
  using System.GCs;
  using System.Runtime.CompilerServices;

  /// <summary>
  /// Abstraction for information about the stack height.  This is currently
  /// only used by the logging undo code for determining if a pointer write
  /// occurred in stack space allocated after the tryall section began.
  ///
  /// StackHeight does not record information about the call stack.
  ///
  /// The current implementation is hardwired to a stack model where the stack
  /// is a single contiguous piece of memory that grows by putting smaller
  /// values into the stack pointer.
  /// </summary>
  [RequiredByBartok]
  internal struct StackHeight {
      /// <summary>
      /// Interpret the pointer as a stack pointer to determine the stack
      /// height.
      /// </summary>
      /// <param name="stackPointer">Pointer into the stack.</param>
      /// <returns>The stack height of the location pointed to by the
      /// argument.</returns>
      internal StackHeight(UIntPtr stackPointer) {
          VTable.Assert(stackPointer == UIntPtr.Zero
                        || (PageTable.Type(PageTable.Page(stackPointer))
                            == PageType.Stack));
          this.stackPointer = stackPointer;
      }

      /// <summary>
      /// Interpret the pointer as a stack pointer to determine the stack
      /// height.
      /// </summary>
      /// <param name="stackPointer">Pointer into the stack.</param>
      /// <returns>The stack height of the location pointed to by the
      /// argument.</returns>
      public static explicit operator StackHeight(UIntPtr stackPointer) {
          return new StackHeight(stackPointer);
      }

      /// <summary>
      /// Get the current stack height.
      /// </summary>
      /// <returns>The current stack height.</returns>
      [Intrinsic]
      internal static extern StackHeight GetStackHeight();

      /// <summary>
      /// Check if the first stack height represents a deeper location on the
      /// stack.
      /// </summary>
      /// <param name="first">The first stack height to compare.</param>
      /// <param name="second">The second stack height to compare.</param>
      /// <returns>True iff the first height is deeper in the stack than the
      /// second height.</returns>
      internal static bool Deeper(StackHeight first, StackHeight second) {
          VTable.Assert(first.stackPointer != UIntPtr.Zero);
          VTable.Assert(second.stackPointer != UIntPtr.Zero);
          return first.stackPointer <= second.stackPointer;
      }

      public override string ToString() {
          return stackPointer.ToString();
      }

      /// <summary>
      /// The value of the stack pointer when the stack height was taken.
      /// </summary>
      private UIntPtr stackPointer;
  }
}
