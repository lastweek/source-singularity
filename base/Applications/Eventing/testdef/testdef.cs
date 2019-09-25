// ----------------------------------------------------------------------------
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
// ----------------------------------------------------------------------------

using System;
using System.Runtime.CompilerServices;
using Microsoft.Singularity.Transform;
using Microsoft.Singularity.Eventing;

namespace Microsoft.Singularity
{

    public class EventEnumAttribute : Attribute
    {
      // mark classes & methods for eventing
    }
        
    [Event]
    public abstract class TestEv : EventSource
    {
        [Event]
        public abstract bool Log(int EventId);
        public static string Log_Format = "EventLogger: EventId={0}";

    }

    [Event]
    public abstract class EvStress1 : EventSource
    {
        [Event]
        public abstract bool Log(int Arg1);
        public static string Log_Format = "EvStress: seq value={0}";
    }

    //
    //  Test source that includes enums, and multiple event functions per same source
    //  The declaration of the schema for enum is still manual, but the rest of the code can leverage
    //  the existing codegen support
    //

    [Event]
    public abstract class EvTest2 : EventSource
    {
        [Event]
        public abstract bool SaveEvent(int Arg1, MyEnum en);
        public static string SaveEvent_Format = "testenum: arg={0}, enum=[{1}]";

        [Event]
        public abstract bool SaveEventFlags(int Arg1, int Arg2, MyFlagsEnum flag );
        public static string SaveEventFlags_Format = "FlagsEnum: arg={0}, {1}; enum=[{2}]";

        [Event]
        public abstract bool SaveEventCombination(int Arg1, int Arg2, MyEnum en, MyFlagsEnum flag);
        public static string SaveEventCombination_Format = "Combinations: arg={0},{1}; enum=[{2}], Flags = [{3}]";

        [EventEnum] 
        public enum MyEnum{
            Val1,
            Val2
        };

        public static UIntPtr MyEnum_Handle;

        [EventEnum] 
        public enum MyFlagsEnum{
            Flag0001 = 0x0001,
            Flag0008 = 0x0008,
            FlagdifferentSize = 16,
        };

        public static UIntPtr MyFlagsEnum_Handle;

        public override void RegisterEnumSymbols()
        {
            base.RegisterEnumSymbols();

            if (HostController.RegisterEnum("MyEnum", DataType.__int32, ref MyEnum_Handle)) {

                HostController.RegisterEnumValue(MyEnum_Handle, "Val1", (UInt64)MyEnum.Val1, 0);
                HostController.RegisterEnumValue(MyEnum_Handle, "Val2", (UInt64)MyEnum.Val2, 0);
            }

            if (HostController.RegisterEnum("MyFlagsEnum", DataType.__int32, ref MyFlagsEnum_Handle)) {

                HostController.RegisterEnumValue(MyFlagsEnum_Handle, "Flag0001", (UInt64)MyFlagsEnum.Flag0001, (byte)'A');
                HostController.RegisterEnumValue(MyFlagsEnum_Handle, "Flag0008", (UInt64)MyFlagsEnum.Flag0008, (byte)'B');
                HostController.RegisterEnumValue(MyFlagsEnum_Handle, "FlagdifferentSize", (UInt64)MyFlagsEnum.FlagdifferentSize, (byte)'Z');
            }
        }
    }
}
