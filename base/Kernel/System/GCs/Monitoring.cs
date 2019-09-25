////////////////////////////////////////////////////////////////////////////////
//
//  Microsoft Research Singularity
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
//  File:  Monitoring.cs
//
//  This is a dummy file used in the generation of the NullRuntime
//  See  Applications\NullRuntime Makefile for reference 

using System; 

namespace Microsoft.Singularity
{
    [CLSCompliant(false)]
     public class Monitoring
    {
            public struct Provider {
                public const ushort GC = 25;
            }
            
       	    public static void Log(ushort provider, ushort type) 
            {
            }

    }
}
