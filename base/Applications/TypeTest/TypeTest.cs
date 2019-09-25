////////////////////////////////////////////////////////////////////////////////
//
//  Microsoft Research Singularity
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
//  Note:   Simple Singularity test program.
//
using Microsoft.Singularity.V1.Services;
using System;
using System.Runtime.CompilerServices;
using System.Threading;

using Microsoft.SingSharp;

using System.Reflection;
using Microsoft.Singularity.Io;
using Microsoft.Singularity.Directory;
using Microsoft.Singularity.Channels;

using Microsoft.Singularity.Channels;
using Microsoft.Contracts;
using Microsoft.SingSharp.Reflection;
using Microsoft.Singularity.Applications;
using Microsoft.Singularity.Io;
using Microsoft.Singularity.Configuration;
[assembly: Transform(typeof(ApplicationResourceTransform))]

namespace Microsoft.Singularity.Applications
{
    [ConsoleCategory(DefaultAction=true)]
    internal class Parameters {
        [InputEndpoint("data")]
        public readonly TRef<UnicodePipeContract.Exp:READY> Stdin;

        [OutputEndpoint("data")]
        public readonly TRef<UnicodePipeContract.Imp:READY> Stdout;

        [BoolParameter( "help", Default=false, HelpMessage="Display Extended help message.")]
        internal bool doHelp;
        
        [StringParameter( "path", Position=0, Mandatory=true)]
        internal string nsPath;

        [LongParameter( "contract", Position=1, Mandatory=true)]
        internal long contractNum;
        
        reflective internal Parameters();

        internal int AppMain() {
            return TypeTest.AppMain(this);
        }
    }

    contract DummyContract : ServiceContract {
    }

    rep struct TestStruct {
        int x;
        int y;

        public TestStruct(int a, int b) { x = a; y = b; }
    }

    public class NS : ITracked {
        
        DirectoryServiceContract.Imp:Ready! ns;

        public NS() {
            this.ns = DirectoryService.NewClientEndpoint();
            base();
        }

        public ServiceContract.Exp Bind(string! path, [Claims] ServiceContract.Exp! ep) 
        {
            char[] in ExHeap p = Bitter.FromString2(path);

            expose (this) {
                ns.SendBind(p, ep);
                switch receive {
                case ns.AckBind():
                    return null;

                case ns.NakBind(reject, error):
                    return reject;

                case ns.ChannelClosed():
                    throw new Exception("ns channel closed");
                }
            }
        }

        public void Dispose() {
            delete this.ns;
        }

        void ITracked.Expose() {}
        void ITracked.UnExpose() {}
        void ITracked.Acquire() {}
        void ITracked.Release() {}
    }

    public class TypeTest
    {
        internal static int AppMain(Parameters! config)
        {
            if (config.doHelp) {
                Console.WriteLine("typetest <nspath> contract-num");
                Console.WriteLine("  where contract-nums are:");
                Console.WriteLine("  0 SoundDeviceContract");
                Console.WriteLine("  1 DiskDeviceContract");
                Console.WriteLine("  2 DummyContract");
                Console.WriteLine("  3 Downcast Imp contract");
                return 1;
            }

            int contractNum = (int) config.contractNum; 

            NS ns = new NS();

            string path = (!)config.nsPath;
            Console.WriteLine("Trying to lookup {0} with contract {1}", path, contractNum);

            ServiceContract.Exp reject;

            switch (contractNum) {
            case 0:
                {
                    Console.WriteLine("Allocating SoundDevice Channel");
                    SoundDeviceContract.Exp! exp;
                    SoundDeviceContract.Imp! imp;
                    SoundDeviceContract.NewChannel(out imp, out exp);
                    reject = ns.Bind(path, exp);
                    delete imp;
                    break;
                }
            case 1:
                {
                    Console.WriteLine("Allocating DiskDevice Channel");
                    DiskDeviceContract.Exp! exp;
                    DiskDeviceContract.Imp! imp;
                    DiskDeviceContract.NewChannel(out imp, out exp);
                    reject = ns.Bind(path, exp);
                    delete imp;
                    break;
                }
            case 2:
                {
                    Console.WriteLine("Allocating Channel");
                    DummyContract.Exp! exp;
                    DummyContract.Imp! imp;
                    DummyContract.NewChannel(out imp, out exp);
                    reject = ns.Bind(path, exp);
                    delete imp;
                    break;
                }
            case 3:
                {
                    Console.WriteLine("Doing Imp cast test");
                    DummyContract.Exp! exp;
                    DummyContract.Imp! imp;
                    DummyContract.NewChannel(out imp, out exp);
                    Endpoint! upcast = imp;

                    DummyContract.Imp imp2 = upcast as DummyContract.Imp;
                    if (imp2 == null) {
                        Console.WriteLine("Downcast to Imp failed");
                    }
                    else {
                        Console.WriteLine("Downcast to Imp succeeded");
                    }
                    DiskDeviceContract.Imp imp3 = upcast as DiskDeviceContract.Imp;
                    if (imp3 == null) {
                        Console.WriteLine("Downcast to bad Imp failed (GOOD)");
                    }
                    else {
                        Console.WriteLine("Downcast to bad Imp succeeded (BAD)");
                    }

                    DummyContract.Exp exp4 = upcast as DummyContract.Exp;
                    if (exp4 == null) {
                        Console.WriteLine("Downcast to Exp failed (GOOD)");
                    }
                    else {
                        Console.WriteLine("Downcast to Exp succeeded (BAD)");
                    }
                    delete exp;
                    delete imp;
                    reject = null;
                    break;
                    
                }
            default:
                Console.WriteLine("Unsupported contract {0}", contractNum);
                reject = null;
                break;
            }

            if (reject == null) {
                Console.WriteLine("Bind succeeded!");
            }
            else {
                Console.WriteLine("Bind failed!");
                delete reject;
            }

            ns.Dispose();

            Console.WriteLine("TypeTest exiting.");
            return 0;
        }
    }
}
