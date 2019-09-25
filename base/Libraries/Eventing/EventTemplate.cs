// ----------------------------------------------------------------------------
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
// ----------------------------------------------------------------------------

using System;
using System.Runtime.CompilerServices;
using Microsoft.Singularity.Transform;
using Microsoft.Singularity.Eventing;
using Microsoft.Singularity.V1.Services;

// patterns
namespace Microsoft.Singularity.EventTemplate
{
    [Pattern][Data]
    public struct EachParam
    {
    }

    [Pattern][EventEnum]
    public enum BasicEnum
    {
    }

    [Pattern]
    public class EachParam_DataType
    {
        public static readonly ushort TypeID = 0;
    }

    [Pattern]
    [Event]
    [Template]
    public abstract class EachSourceClass : EventSource
    {
        [Pattern]
        [Event]
        public abstract bool EachLogMethod([Case][EventEnum]BasicEnum eachBasicEnumParam,
            [Case][Data]EachParam eachParam);

        // temporary static string for each method that defines a printf format
        // todo: move into attribute parameters
        public static string EachLogMethod_Format;

        // generate template code

        new public static uint ControlFlag;

        // separate flag for each meth
        public static readonly uint EachLogMethod_Flag;

        // separate handle for the type defined for each meth
        public static UIntPtr EachLogMethod_Handle;

        public static UIntPtr BasicEnum_Handle;
        
        // class constructor to intialize flag bits
        static EachSourceClass()
        {
            ControlFlag = 0;
            uint flag = 0x10000;
            Transform.For("EachLogMethod");
                EachLogMethod_Format = null;
                EachLogMethod_Flag = flag;
                BasicEnum_Handle = 0;
                
                flag = flag << 1;
                if (flag == 0) {
                    throw new Exception("Flag overflow - too many methods in EachSourceClass");
                }
            Transform.EndFor();
        }

        // template for static creation method
        new public static EachSourceClass Create(string sourcename,
                                                 uint size,
                                                 uint storageOptions,
                                                 uint sourceFlags)
        {
            EventingStorage storage = EventingStorage.CreateLocalStorage(storageOptions,
                                                                         size);

            if (storage == null) {

                DebugStub.WriteLine("Failure to create local storage " + sourcename);
                DebugStub.Break();
                return null;                                                  
            }
            
            EachSourceClass Source = new EachSourceClass_Impl(sourcename, 
                                                              storage,
                                                              sourceFlags);

            if (Source != null) {

                if (!Source.Register()) {

                    DebugStub.WriteLine("Error initializing the source " + sourcename);
                    return null;
                }
            }

            return Source;
            
        }

        // struct to hold event parameters for each method
        public struct EachLogMethod_Event
        {
            public EachParam eachParam;
            public int eachBasicEnumParam;
        }

        internal EachSourceClass(string sourceName, EventingStorage storage, uint controlFlags) 
          :base(sourceName, storage, controlFlags) {}

    }

  [Template]
  internal class EachSourceClass_Impl : EachSourceClass
  {

        [NoHeapAllocation]
        public override bool EachLogMethod([Case][EventEnum]BasicEnum eachBasicEnumParam,
                                           [Case][Data]EachParam eachParam)
        {
            if ((ControlFlags & EachLogMethod_Flag) != 0) {

                unsafe {

                    EachLogMethod_Event Event;

                    Transform.For("eachParam");
                        Event.eachParam = eachParam;
                    Transform.EndFor();

                    Transform.For("eachBasicEnumParam");
                        Event.eachBasicEnumParam = (int)eachBasicEnumParam;
                    Transform.EndFor();

                    return (LogEntry(ControlFlags, 
                                     EachLogMethod_Handle, 
                                     (byte *)&Event, 
                                     sizeof(EachLogMethod_Event)) != 0);
                }
            }

            return false;
        }

        public override bool Register() {

            if (!base.Register()) {

                return false;
            }

            if (HostController == null) {

                return false;
            }

            RegisterEnumSymbols();
            
            DataType2 dt2 = new DataType2();
            
            string s = "EachSourceClass";
            Transform.For("EachLogMethod");
                string format = EachLogMethod_Format != null ? EachSourceClass.EachLogMethod_Format : "{0}";

                if (HostController.RegisterEvent(s + ".EachLogMethod", format, ref EachLogMethod_Handle)) {

                    DebugStub.WriteLine("register event succeeded");

                    
                    Transform.For("eachParam");
                        HostController.RegisterEventField(EachSourceClass.EachLogMethod_Handle, 
                                                          "eachParam", 
                                                          0, 
                                                          dt2.__EachParam);
                    Transform.EndFor();

                    //
                    // HACK!!!!! Some instruction is needed here, otherwise, the transform
                    // will merge the enumeration below with the one above
                    // producing a mismatch in the order of argumets in the structure declaration
                    //
                    DebugStub.WriteLine("Registering enums");
                    
                    Transform.For("eachBasicEnumParam");

                        HostController.RegisterEventGenericField(EachSourceClass.EachLogMethod_Handle, 
                                                          "eachBasicEnumParam", 
                                                          0, 
                                                          sizeof(int),  
                                                          BasicEnum_Handle);
                    Transform.EndFor();
                    
                } else {

                    // The event might have been registered already
                    // Check whether we foundit already in the table or not

                    if (EachSourceClass.EachLogMethod_Handle == 0) {
                        return false;
                    }
                }
            Transform.EndFor();

            return true;
        }

        internal EachSourceClass_Impl(string sourceName, EventingStorage storage, uint controlFlags) 
          :base(sourceName, storage, controlFlags) {}
  }
}
