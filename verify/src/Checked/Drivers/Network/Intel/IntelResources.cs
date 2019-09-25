///////////////////////////////////////////////////////////////////////////////
//
//  Microsoft Research Singularity
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//

// #define TYAN_MOTHERBOARD_HACK

using Microsoft.Singularity.Channels;
//using Microsoft.Singularity.Configuration;
using Microsoft.Singularity.Directory;
//using Microsoft.Singularity.Extending;
using Microsoft.Singularity.Io;
using Microsoft.Singularity.Io.Net;
//using Microsoft.SingSharp.Reflection;
using Microsoft.Singularity.Drivers;

using System;

//[assembly: Transform(typeof(DriverResourceTransform))]
namespace Microsoft.Singularity.Drivers.Network.Intel
{
    internal enum CardType : int
    {
        I82541PI,
        I82545GM
    }

    // Common interface for all intel resource classes
    internal interface IntelResources
    {
        IoMemoryRange imr {
            get;
        }

        IoIrqRange irq {
            get;
        }

        string CardName {
            get;
        }

        CardType CardType {
            get;
        }

        TRef/*<ExtensionContract.Exp>*/ ec {
            get;
        }

        TRef/*<ServiceProviderContract.Exp>*/ nicsp {
            get;
        }
    }

#if false
    // Intel Pro/1000 GT - 82541 PI
    [DriverCategory]
    [Signature("pci/ven_8086&dev_107c&cc_0200")]
    internal class Intel82541piResources : DriverCategoryDeclaration, IntelResources
    {
#if !TYAN_MOTHERBOARD_HACK
        [IoMemoryRange(0, Default = 0xfebe0000, Length = 0x20000)]
        internal IoMemoryRange imrField;

        [IoMemoryRange(1, Default = 0xfebe0000, Length = 0x20000)]
        internal IoMemoryRange flashField; // this is unused, but we must declare itres

        [IoPortRange(2, Default = 0xec00, Length = 0x40)]
        internal IoPortRange ioPortCsrField;

        [IoIrqRange(6, Default = 0x05, Shared = true)]
        internal IoIrqRange irqField;
#else
        [IoMemoryRange(0, Default = 0xb0320000, Length = 0x20000)]
        internal IoMemoryRange imrField;

        [IoMemoryRange(1, Default = 0xb0300000, Length = 0x20000)]
        internal IoMemoryRange flashField; // this is unused, but we must declare itres

        [IoPortRange(2, Default = 0x3000, Length = 0x40)]
        internal IoPortRange ioPortCsrField;

        [IoIrqRange(6, Default = 0x05, Shared = true)]
        internal IoIrqRange irqField;
#endif
        [ExtensionEndpoint]
        internal TRef/*<ExtensionContract.Exp>*/ ecField;

        [ServiceEndpoint(typeof(NicDeviceContract))]
        internal TRef/*<ServiceProviderContract.Exp>*/ nicspField;

        // proerties
        public IoMemoryRange imr {
            get {
                return imrField;
            }
        }

        public IoIrqRange irq {
            get{
                return irqField;
            }
        }

        public TRef/*<ExtensionContract.Exp>*/ ec {
            get{
                return ecField;
            }
        }

        public TRef/*<ServiceProviderContract.Exp>*/ nicsp {
            get{
                return nicspField;
            }
        }

        public string CardName
        {
            get {
                return "82541 PI";
            }
        }

        public CardType CardType
        {
            get {
                return CardType.I82541PI;
            }
        }

        internal int DriverMain(string instance)
        {
            return IntelController.DriverMain(this);
        }
    }

    //  Intel Pro/1000 GT 82545 GM
    [DriverCategory]
    [Signature("pci/ven_8086&dev_1026&cc_0200")]
    internal class Intel82545gmResources : DriverCategoryDeclaration, IntelResources
    {
        [IoMemoryRange(0, Default = 0xfebe0000, Length = 0x20000)]
        internal readonly IoMemoryRange imrField;

        [IoMemoryRange(1, Default = 0xfebe0000, Length = 0x10000)]
        internal readonly IoMemoryRange flashField; // this is unused, but we must declare itres

        [IoPortRange(2, Default = 0xec00, Length = 0x40)]
        internal readonly IoPortRange ioPortCsrField;

        [IoIrqRange(6, Default = 0x05, Shared = true)]
        internal readonly IoIrqRange irqField;

        [ExtensionEndpoint]
        internal TRef/*<ExtensionContract.Exp>*/ ecField;

        [ServiceEndpoint(typeof(NicDeviceContract))]
        internal TRef/*<ServiceProviderContract.Exp>*/ nicspField;

        // proerties
        public IoMemoryRange imr {
            get {
                return imrField;
            }
        }

        public IoIrqRange irq {
            get{
                return irqField;
            }
        }

        public TRef/*<ExtensionContract.Exp>*/ ec {
            get{
                return ecField;
            }
        }

        public TRef/*<ServiceProviderContract.Exp>*/ nicsp {
            get{
                return nicspField;
            }
        }

        public string CardName
        {
            get {
                return "82545 GM";
            }
        }

        public CardType CardType
        {
            get {
                return CardType.I82545GM;
            }
        }

        internal int DriverMain(string instance)
        {
            return IntelController.DriverMain(this);
        }
    }
#endif
}
