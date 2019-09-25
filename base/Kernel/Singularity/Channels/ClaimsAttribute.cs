////////////////////////////////////////////////////////////////////////////////
//
//  Microsoft Research Singularity
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
//  File:   ClaimsAttribute.cs
//
//  Note: File is part of Sing# runtime files and copied into Singularity tree
//        whenever a new version of Sing# is dropped.
//        Coordinate any changes with Sing# team.
//

using System;


namespace Microsoft.SingSharp
{
    /// <summary>
    /// Can be used on parameters of ITracked type to override the default Borrowed semantics.
    ///
    /// Means that parameter ownership is not returned by method.
    ///
    /// If the attribute appears on an instance method, the attribute applies to the receiver parameter.
    /// </summary>
    [ AttributeUsage(AttributeTargets.Parameter | AttributeTargets.Method, AllowMultiple = false)]
    public class ClaimsAttribute : Attribute
    {
    }


    /// <summary>
    /// Can be used on return of ITracked type to override the default Owned semantics.
    /// 
    /// Means that the returned value is part of the 'receivers' representation and cannot outlive the receiver.
    ///
    /// </summary>
    [ AttributeUsage(AttributeTargets.ReturnValue, AllowMultiple = false)]
    public class BorrowedAttribute : Attribute 
    {
    }
}
