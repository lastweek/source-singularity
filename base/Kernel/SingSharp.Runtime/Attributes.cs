using System;
using System.Collections;

//---------------------------------------------------------------------------
//SingSharp Library
//---------------------------------------------------------------------------

namespace Microsoft.SingSharp {



  /// <summary>
  /// Marks methods that check should enforce context restrictions on
  /// </summary>
  [ AttributeUsage(AttributeTargets.Method | AttributeTargets.Delegate, AllowMultiple = true)]
  public class ContextRestrictionAttribute : Attribute {
  }


  /// <summary>
  /// Context restriction that enforces that a method does not perform allocations and does not
  /// call methods that perform allocations.
  /// </summary>
  [ AttributeUsage(AttributeTargets.Method | AttributeTargets.Delegate, AllowMultiple = true)]
  public class NoAllocateAttribute : ContextRestrictionAttribute {
  }

  /// <summary>
  /// Context restriction that enforces that a method does not block and does not call methods that
  /// might block. It's strictly more restrictive than NoAllocate, since allocation can cause blocking.
  /// </summary>
  [ AttributeUsage(AttributeTargets.Method | AttributeTargets.Delegate, AllowMultiple = true)]
  public class NoBlockingAttribute : NoAllocateAttribute {
  }

  /// <summary>
  /// Marks a struct as a message.
  /// </summary>
  public sealed class MessageAttribute : Attribute {
    public enum Direction {
      In,
      Out,
      Both
    }

    public MessageAttribute(Direction direction) {
    }
  }


  /// <summary>
  /// Marks a rep struct as not containing any pointers.
  /// </summary>
  public sealed class PointerFreeAttribute : Attribute {
  }

  /// <summary>
  /// Marks the protocolstate as a parallel (All) state
  /// </summary>
  public sealed class ProtocolParallelStateAttribute : Attribute {
    public ProtocolParallelStateAttribute() {}
  }


  /// <summary>
  /// Marks a the start state of a protocol.
  /// </summary>
  public sealed class ProtocolStartStateAttribute : Attribute {
    public ProtocolStartStateAttribute() {}
  }


  /// <summary>
  /// Send(tag) annotates a send method on Imp and Exp types, marking that the corresponding message
  /// is sent on the receiver endpoint
  /// </summary>
  public class SendAttribute : Attribute {
    public SendAttribute(int tag) {}
  }

  /// <summary>
  /// Receive(tag) annotates a receive method on Imp and Exp types, marking that the corresponding message
  /// is received.
  /// </summary>
  public class ReceiveAttribute : Attribute {
    public ReceiveAttribute(int tag) {}
  }


  /// <summary>
  /// Annotates an endpoint parameter of a method. Indicates that the endpoint is in the protocol 
  /// state specified by the given type argument on entry to the method.
  /// </summary>
  public class PreStateAttribute : Attribute {
    public PreStateAttribute(System.Type @state) {}
  }


  /// <summary>
  /// Annotates an endpoint parameter of a method. Indicates that the endpoint is in the protocol 
  /// state specified by the given type argument on exit of the method.
  /// </summary>
  public class PostStateAttribute : Attribute {
    public PostStateAttribute(System.Type @state) {}
  }


  #region Obsolete. Get rid of these and switch to ITracked and Claims tracking
  /// <summary>
  /// Annotates a method result or out parameter to indicate that the method transfers ownership of the
  /// endpoint to the caller. The bind is from the caller's perspective. The callee must view it as
  /// an unbind.
  /// </summary>
  public class BindEndpointAttribute : Attribute {
    public BindEndpointAttribute() {}
  }

  /// <summary>
  /// Annotates a method parameter to indicate that the caller transfers ownership of the
  /// endpoint to the callee. The unbind is from the caller's perspective. The callee must view it as
  /// a bind.
  /// </summary>
  public class UnbindEndpointAttribute : Attribute {
    public UnbindEndpointAttribute() {}
  }
  #endregion


  /// <summary>
  /// Marks static fields that hold select receive patterns. The argument
  /// is the actual int[][] pattern array used in the initializer.
  /// 
  /// Each case row is a separate attribute.
  /// </summary>
  [ AttributeUsage(AttributeTargets.Field, AllowMultiple = true)]
  public class SelectReceivePatternAttribute : Attribute {
    public SelectReceivePatternAttribute(int row, int[] pattern) {}
  }


  [ AttributeUsage(AttributeTargets.Assembly, AllowMultiple = true) ]
  public class LinkPortAttribute : Attribute {
    public LinkPortAttribute(System.Type importPort, System.Type exportPort) {}
  }

  // a dummy attribute used for compiling type extensions
  // (in case the real Bartok version is inaccessible)
  [ AttributeUsage(AttributeTargets.Class|AttributeTargets.Struct|AttributeTargets.Interface) ]
  public sealed class MixinAttribute : Attribute {
    internal Type option;
    public MixinAttribute(Type type) {
      this.option = type;
    }
  }
  // a dummy attribute used for compiling type extensions
  // (in case the real Bartok version is inaccessible)
  [ AttributeUsage(AttributeTargets.Method) ]
  public sealed class MixinExtendAttribute : Attribute {
    internal string name;
    public MixinExtendAttribute(string name) {
      this.name = name;
    }
  }
}

#if CCINamespace
namespace Microsoft.Cci.TypeExtensions {
#else
namespace System.Compiler.TypeExtensions {
#endif
  /// <summary>
  /// Marks a class as a process contract
  /// </summary>
  public interface IChannelContract {
  }

  /// <summary>
  /// Marks a struct as a rep struct
  /// </summary>
  public interface IRepStruct {
  }

  /// <summary>
  /// Marks a struct as a rep struct type parameter
  /// </summary>
  public interface IRepStructParameter {
  }

  /// <summary>
  /// Marks a struct as a message struct
  /// </summary>
  public interface IMessage {
  }

  /// <summary>
  /// Marks a protocol state as a protocol state
  /// </summary>
  public interface IProtocolState {
  }

  /// <summary>
  /// Marks a signature class as a signature
  /// </summary>
  public interface ISignature {
  }

  /// <summary>
  /// Marks a part class as an import port
  /// </summary>
  public interface IImportPort 
  {
  }

  /// <summary>
  /// Marks a part class as an export port
  /// </summary>
  public interface IExportPort 
  {
  }

}

namespace System.Compiler {
    /// <summary>
    /// Used to mark Template classes so Bartok can ignore them.
    /// If the name or namespace changes, we need to update bartok.
    /// </summary>
    public interface ITemplate {
    }
}

