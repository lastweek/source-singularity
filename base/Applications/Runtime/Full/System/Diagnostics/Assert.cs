// ==++==
//
//   Copyright (c) Microsoft Corporation.  All rights reserved.
//
// ==--==
namespace System.Diagnostics
{
    using System;
    using System.Reflection;
    using System.Runtime.CompilerServices;
    using Microsoft.Singularity;

    // Class which handles code asserts.  Asserts are used to explicitly protect
    // assumptions made in the code.  In general if an assert fails, it indicates
    // a program bug so is immediately called to the attention of the user.
    //| <include path='docs/doc[@for="Assert"]/*' />
    internal class Assert
    {
        private static AssertFilter[] ListOfFilters = null;
        private static int iNumOfFilters = 0;
        private static int iFilterArraySize = 0;
        private static AssertFilter DefFil = new DefaultFilter();

        // AddFilter adds a new assert filter. This replaces the current
        // filter, unless the filter returns FailContinue.
        //
        //| <include path='docs/doc[@for="Assert.AddFilter"]/*' />
        public static void AddFilter(AssertFilter filter)
        {
            if (iFilterArraySize <= iNumOfFilters) {
                    AssertFilter[] newFilterArray = new AssertFilter [iFilterArraySize+2];

                    if (iNumOfFilters > 0)
                        Array.Copy(ListOfFilters, newFilterArray, iNumOfFilters);

                    iFilterArraySize += 2;

                    ListOfFilters = newFilterArray;
            }

            ListOfFilters [iNumOfFilters++] = filter;
        }

        // Called when an assertion is being made.
        //
        //| <include path='docs/doc[@for="Assert.Check"]/*' />
        public static void Check(bool condition, String conditionString, String message)
        {
            if (!condition) {
                Fail (conditionString, message);
            }
        }


        //| <include path='docs/doc[@for="Assert.Fail"]/*' />
        public static void Fail(String conditionString, String message)
        {
            // Run through the list of filters backwards (the last filter in the list
            // is the default filter. So we're guaranteed that there will be at least
            // one filter to handle the assert.

            int iTemp = iNumOfFilters;
            while (iTemp > 0) {

                AssertFilters iResult = ListOfFilters [--iTemp].AssertFailure (conditionString, message);

                if (iResult == AssertFilters.FailDebug) {
#if SINGULARITY_KERNEL
                    DebugStub.Break();
#elif SINGULARITY_PROCESS
                    VTable.DebugBreak();
#endif
                    break;
                }
                else if (iResult == AssertFilters.FailTerminate)
#if SINGULARITY_KERNEL
                    Kernel.Shutdown(-1);
#elif SINGULARITY_PROCESS
                    AppRuntime.Stop(-1);
#endif
                else if (iResult == AssertFilters.FailIgnore)
                    break;

                // If none of the above, it means that the Filter returned FailContinue.
                // So invoke the next filter.
            }

        }

      // Called when an assertion fails.
      //
      //| <include path='docs/doc[@for="Assert.ShowDefaultAssertDialog"]/*' />
      public static int ShowDefaultAssertDialog(String conditionString, String message) {
          throw new Exception("System.Diagnostics.Assert.ShowDefaultAssertDialog not implemented in Bartok!");
      }
    }


}
