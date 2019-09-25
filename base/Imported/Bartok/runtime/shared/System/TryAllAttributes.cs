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

  // A method marked as NoLoggingForUndo will not have logging code
  // inserted even if called from a logging context
  [AttributeUsage(AttributeTargets.Assembly | AttributeTargets.Class
                  | AttributeTargets.Struct | AttributeTargets.Constructor
                  | AttributeTargets.Method,
                  Inherited = false)]
  public sealed class NoLoggingForUndoAttribute: Attribute {}

  // A method marked as NonTransactional may NOT be called from a
  // transactional context.  This is statically checked by
  // convert\PropagateLogging.cs
  [AttributeUsage(AttributeTargets.Assembly | AttributeTargets.Class
                  | AttributeTargets.Struct | AttributeTargets.Constructor
                  | AttributeTargets.Method,
                  Inherited = false)]
  public sealed class NonTransactableAttribute: Attribute {}

}
