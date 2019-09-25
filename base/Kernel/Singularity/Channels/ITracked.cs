////////////////////////////////////////////////////////////////////////////////
//
//  Microsoft Research Singularity
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
//  File:   ITracked.cs
//
//  Note: File is part of Sing# runtime files and copied into Singularity tree
//        whenever a new version of Sing# is dropped.
//        Coordinate any changes with Sing# team.
//

using System;

namespace Microsoft.SingSharp
{
  /// <summary>
  /// ITracked is a marker interface that marks a GC type as linearly tracked.
  /// 
  /// Upcasts of a class C deriving from ITracked are only allowed if 
  /// a) the target also derives from ITracked, in which case linear tracking continues, or
  /// b) the target is an interface deriving from IBorrowed. In this case, the resulting value
  ///    is prevented from escaping the static scope it is in. The checker must make sure that the
  ///    original tracked object isn't used until the borrowed reference dies.
  ///  By default, any parameter of type ITracked is treated as borrowed, meaning that it must
  ///  be owned on entry and ownership is returned on exit.
  ///
  ///  By default, any out parameter or return value of type ITracked is interpreted as passing fresh
  ///  ownership from callee to caller.
  ///
  ///  The only overrides needed are for parameters that claim ownership. The Claims attribute below serves
  ///  that purpose.
  /// </summary>
  public interface ITracked {
    
    /// <summary>
    /// Called when a thread releases a tracked object so it can be acquired by another thread.
    /// Gives implementor of tracked type chance to
    /// know that current thread no longer owns this tracked resource
    ///
    /// Normal clients should not call this method.
    /// </summary>
    void Release();

    /// <summary>
    /// Called when a thread acquired a tracked object not owned by it. Gives implementor of tracked type chance to
    /// know that current thread now owns this tracked resource.
    ///
    /// Note, this method cannot block.
    ///
    /// Normal clients should not call this method.
    /// </summary>
    void Acquire();

    /// <summary>
    /// Called to delete the associated resource.
    /// </summary>
    void Dispose();

    /// <summary>
    /// This is a marker method called at the beginning of expose blocks.
    /// Expose blocks provide scoped access to the tracked fields of tracked objects.
    /// </summary>
    void Expose();

    /// <summary>
    /// This is a marker method called at the end of an expose blocks.
    /// Expose blocks provide scoped access to the tracked fields of tracked objects.
    /// </summary>
    void UnExpose();
  }


  /// <summary>
  /// Marker interface for interfaces that custom heap pointers can be boxed to, while
  /// preventing the loss of ownership tracking.
  /// Upcasts from an interface deriving from IBorrowed are only allowed if target interface
  /// also derives from IBorrowed.
  /// </summary>
  public interface IBorrowed {
  }
}
