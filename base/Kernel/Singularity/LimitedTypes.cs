////////////////////////////////////////////////////////////////////////////////
//
//  Microsoft Research Singularity
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//

using System;

public class LimitedTypes
{
    // A list of types that Bartok's VTable class should
    // initialize as a limited type.
    public static Type[] TypeList {
        get {
            return new Type[] {
                typeof(System.DateTime),
                typeof(System.TimeSpan),
                typeof(System.SchedulerTime),

                typeof(System.Type),
                typeof(System.String),
                typeof(System.BitConverter),
                typeof(System.Math),
                typeof(System.VTable)
            };
        }
    }
}
