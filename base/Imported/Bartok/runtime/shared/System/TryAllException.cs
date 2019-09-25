//
// Copyright (c) Microsoft Corporation.   All rights reserved.
//

/*******************************************************************/
/*                           WARNING                               */
/* This file should be identical in the Bartok and Singularity     */
/* depots. Master copy resides in Bartok Depot. Changes should be  */
/* made to Bartok Depot and propagated to Singularity Depot.       */
/*******************************************************************/


// This file contains the runtime support code for tryall support.

namespace System {
  public sealed class TryAllFakeException : Exception {}
  public sealed class AtomicFakeException : Exception {}
}
