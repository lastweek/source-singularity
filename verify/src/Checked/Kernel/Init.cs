//
// Copyright (c) Microsoft Corporation.  All rights reserved.
//

using System.Runtime.CompilerServices;
using kernel;

namespace kernel
{

internal class InitThread: ThreadStart //, Microsoft.Singularity.Io.Net.NicDeviceEventContract
{
    [InterruptsDisabled]
    internal InitThread(): base(true)
    {
    }

    public override void Run()
    {
        System.DebugStub.Init();
        System.DebugStub.Print("InitThread@" + Kernel.CurrentThread + ". ");
        System.VTable.Initialize();
        System.DebugStub.Print("Static initializers done. ");

        Kernel.kernel.NewThread(new IoThread());

        Semaphore[] semaphores = new Semaphore[2];
        KeyboardDriver keyboardDriver = new KeyboardDriver(Kernel.kernel, semaphores);

        semaphores[0] = Kernel.kernel.NewSemaphore(0);
        semaphores[1] = Kernel.kernel.NewSemaphore(0);

        for (int i = 0; i < semaphores.Length; i++) {
            Semaphore s = Kernel.kernel.NewSemaphore(0);
            semaphores[i] = s;
            Kernel.kernel.NewThread(
                new Shell(
                    keyboardDriver,
                    s,
                    (uint)(80 * 41 + 80 * 4 * i),
                    (uint)(80 * 41 + 80 * 4 * i + 80 * 3),
                    (uint)(0x2000 + 0x1000 * i + 0x0f00)
                    ));
        }

        Kernel.kernel.NewThread(keyboardDriver);

        System.DebugStub.Print("InitThread done. ");
        Kernel.kernel.NewSemaphore(0).Wait();
    }
}

} // kernel
