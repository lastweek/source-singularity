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
    public sealed class UserMagic
    {
        public static UIntPtr addressOf(Object o)
        {
            return Microsoft.Bartok.Runtime.Magic.addressOf(o);
        }
    }
}
