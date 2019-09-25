/*******************************************************************/
/*                           WARNING                               */
/* This file should be identical in the Bartok and Singularity     */
/* depots. Master copy resides in Bartok Depot. Changes should be  */
/* made to Bartok Depot and propagated to Singularity Depot.       */
/*******************************************************************/

//
// Copyright (c) Microsoft Corporation.   All rights reserved.
//

namespace System.GCs {

    internal struct CoCoPageUserValue
    {
        private ushort userValue;
        
        internal CoCoPageUserValue(ushort userValue)
        {
            this.userValue = userValue;
        }
        
        internal ushort Bits
        {
            get {
                return userValue;
            }
        }
        
        internal bool Marked
        {
            get {
                return (userValue&1)!=0;
            }
            set {
                userValue=(ushort)((userValue&~(ushort)1)|(value?(ushort)1:(ushort)0));
            }
        }
        
        internal bool Pinned
        {
            get {
                return (userValue&2)!=0;
            }
            set {
                userValue=(ushort)((userValue&~(ushort)2)|(value?(ushort)2:(ushort)0));
            }
        }
        
        internal int Version
        {
            get {
                return (int)(userValue>>2);
            }
            set {
                userValue=(ushort)((userValue&(ushort)3)|((ushort)(value<<2)));
            }
        }
        
    }

}

