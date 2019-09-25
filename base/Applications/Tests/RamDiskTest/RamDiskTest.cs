///////////////////////////////////////////////////////////////////////////////
//
//  Microsoft Research Singularity
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
//  Note:   Perform short test of some RamDisk and RamDiskClientManager operations.
//          Used MemStress.cs as an application template.
//

using System;
using System.Collections;
using System.Threading;

using Microsoft.Singularity.UnitTest;
using Microsoft.Singularity.V1.Services;

using Microsoft.Contracts;
using Microsoft.SingSharp;
using Microsoft.SingSharp.Reflection;
using Microsoft.Singularity.Applications;
using Microsoft.Singularity.Channels;
using Microsoft.Singularity.Directory;
using Microsoft.Singularity.Configuration;
using Microsoft.Singularity.Io;

using Microsoft.Singularity.Services.RamDisk;
using Microsoft.Singularity.Services.RamDisk.Contracts;

[assembly: Transform(typeof(ApplicationResourceTransform))]

namespace Microsoft.Singularity.Applications
{
    [ConsoleCategory(DefaultAction=true)]
    internal class Parameters {
        [InputEndpoint("data")]
        public readonly TRef<UnicodePipeContract.Exp:READY> Stdin;

        [OutputEndpoint("data")]
        public readonly TRef<UnicodePipeContract.Imp:READY> Stdout;

        reflective internal Parameters();

        internal int AppMain() {
            return RamDiskTest.AppMain(this);
        }
    }

    public class RamDiskTest
    {
        internal static int AppMain(Parameters! config)
        {
            const int diskBytes = 2000000 /*bytes*/;

            RamDiskControlContract.Imp   managerImp = null;
            DirectoryServiceContract.Imp dsImp      = null;
            DiskDeviceContract.Imp       diskImp    = null;
            try {
                managerImp = ConnectToRamDiskClientManager();
                
                string! diskPath = CreateTest(managerImp, diskBytes);
                dsImp = DirectoryService.NewClientEndpoint();
                diskImp = OpenDevice(dsImp, diskPath);
                
                int lastSector = (diskBytes - 1 + RamDisk.SECTOR_SIZE - 1)/RamDisk.SECTOR_SIZE;
                BasicReadWriteTest(diskImp, 0/*sector*/,  RamDisk.SECTOR_SIZE);
                BasicReadWriteTest(diskImp, lastSector,   RamDisk.SECTOR_SIZE);
                BasicReadWriteTest(diskImp, lastSector/2, RamDisk.SECTOR_SIZE);
                for (int size = RamDisk.SECTOR_SIZE; size < diskBytes; size *= 2) {
                    BasicReadWriteTest(diskImp, 0/*sector*/, size);
                }
                BasicReadWriteTest(diskImp, 0/*sector*/, diskBytes);

                BasicReadWriteErrorTest(diskImp, lastSector + 1, RamDisk.SECTOR_SIZE);
                BasicReadWriteErrorTest(diskImp, lastSector, 2*RamDisk.SECTOR_SIZE);
                BasicReadWriteErrorTest(diskImp, 0/*sector*/, diskBytes + RamDisk.SECTOR_SIZE);
                BasicReadWriteErrorTest(diskImp, lastSector/2, (lastSector + 1 - lastSector/2 + 1) * RamDisk.SECTOR_SIZE);

                RandomReadWriteTest(diskImp, diskBytes);

                EnsureDestroyFailsWithInUse(managerImp, diskPath);

                delete diskImp;
                diskImp = null;

                Destroy(managerImp, diskPath, false/*force*/);
                EnsureDoesNotExist(dsImp, diskPath);

                OutOfMemoryTest(managerImp);
            }
            catch (Exception ex) {
                Console.WriteLine("Error: " + ex.Message + "\n" + ex.StackTrace);
            }
            finally {
                delete managerImp;
                delete dsImp;
                delete diskImp;
            }
            return 0;
        }

        private static void BasicReadWriteTest(DiskDeviceContract.Imp:Ready! diskImp,
                                               int                           sector,
                                               int                           size)
        {
            byte[] in ExHeap data = null;
            try {
                data = new[ExHeap] byte[size];
                for (int i = 0; i < data.Length; i++) {
                    data[i] = (byte)i;
                }
                data = Write(diskImp, 0, data);

                delete data;
                data = new[ExHeap] byte[size];
                
                data = Read(diskImp, 0, data);
                for (int i = 0; i < data.Length; i++) {
                    if (data[i] != (byte)i) {
                        throw new Exception(String.Format("Data did not match after write-read sequence: at byte {0} got {1}, expected {2}",
                                                          i, data[i], (byte)i));
                    }
                }
            }
            finally {
                delete data;
            }
        }

        private static void BasicReadWriteErrorTest(DiskDeviceContract.Imp:Ready! imp,
                                                    int                           sector,
                                                    int                           size)
        {
            byte[] in ExHeap data = new[ExHeap] byte[size];
            imp.SendRead(data, 0, (ulong)size, (ulong)sector);
            switch receive {
                case imp.AckRead(outBuffer):
                    delete outBuffer;
                    throw new Exception("RamDisk read operation succeeded where expected to fail");
                case imp.NakRead():
                    break;
                case imp.ChannelClosed():
                    throw new Exception("RamDisk closed channel prematurely");
            }

            data = new[ExHeap] byte[size];
            imp.SendWrite(data, 0, (ulong)size, (ulong)sector);
            switch receive {
                case imp.AckWrite(outBuffer):
                    throw new Exception("RamDisk write operation succeeded where expected to fail");
                case imp.NakWrite():
                    break;
                case imp.ChannelClosed():
                    throw new Exception("RamDisk closed channel prematurely");
            }
        }

        private static void RandomReadWriteTest(DiskDeviceContract.Imp:Ready! diskImp,
                                                int                           diskBytes)
        {
            const int seed = 840799514; // Just an arbitrary value
            const int sectorsToWrite = 1000;
            int numSectors = (diskBytes - 1 + RamDisk.SECTOR_SIZE - 1)/RamDisk.SECTOR_SIZE + 1;
            Random r = new Random(seed);
            ArrayList! visitedSectors = new ArrayList();
            
            byte[]! in ExHeap data = new[ExHeap] byte[RamDisk.SECTOR_SIZE];
            try {
                byte[]! gcData = new byte[RamDisk.SECTOR_SIZE];
                for (int i = 0; i < sectorsToWrite; i++) {
                    int sectorNum = r.Next(numSectors);
                    if (visitedSectors.Contains(sectorNum)) {
                        continue;
                    }
                    else {
                        visitedSectors.Add(sectorNum);
                    }

                    r.NextBytes(gcData);
                    
                    Bitter.FromByteArray(data, 0, RamDisk.SECTOR_SIZE, gcData, 0);
                    data = Write(diskImp, (ulong)sectorNum, data);
                }

                visitedSectors.Clear();

                r = new Random(seed);
                for (int i = 0; i < sectorsToWrite; i++) {
                    int sectorNum = r.Next(numSectors);
                    if (visitedSectors.Contains(sectorNum)) {
                        continue;
                    }
                    else {
                        visitedSectors.Add(sectorNum);
                    }

                    r.NextBytes(gcData);
                    
                    data = Read(diskImp, (ulong)sectorNum, data);
                    for (int byteNum = 0; byteNum < data.Length; byteNum++) {
                        if (data[byteNum] != gcData[byteNum]) {
                            throw new Exception(
                                String.Format("Data did not match after write-read sequence: at sector {0}, byte {1}, got {2}, expected {3}",
                                              sectorNum, byteNum, data[byteNum], gcData[byteNum]));
                        }
                    }
                }
            }
            finally {
                delete data;
            }
        }

        private static RamDiskControlContract.Imp! ConnectToRamDiskClientManager()
        {
            DirectoryServiceContract.Imp! dsExp =
                DirectoryService.NewClientEndpoint();

            RamDiskControlContract.Imp! fccImp;
            RamDiskControlContract.Exp! fccExp;
            RamDiskControlContract.NewChannel(out fccImp, out fccExp);
            try {
                dsExp.SendBind(
                    Bitter.FromString2(
                        RamDiskControlContract.ManagerControlPath
                        ),
                    fccExp);

                switch receive {
                    case dsExp.AckBind():
                        switch receive {
                            case fccImp.Success():
                                return fccImp;
                            case fccImp.ChannelClosed():
                                throw new Exception("RamDisk client manager closed channel prematurely");
                        }
                        // unreached
                    case dsExp.NakBind(exp, errorCode):
                        delete exp;
                        delete fccImp;
                        throw new Exception("RamDisk client manager rejected bind");
 
                    case dsExp.ChannelClosed():
                        delete fccImp;
                        throw new Exception("RamDisk client manager closed channel prematurely");
                }
            }
            finally {
                delete dsExp;
            }
        }
        
        private static void OutOfMemoryTest(RamDiskControlContract.Imp! controller)
        {
            controller.SendCreate(1000000000000L);

            switch receive {
                case controller.CreateSuccess(diskPath):
                    delete diskPath;
                    throw new Exception("Creation of very large disk succeeded where expected to fail with out of memory");
                case controller.Fail(error):
                    if (error != RamDiskContractErrorCode.OutOfMemory) {
                        throw new Exception("Creation of very large disk failed with unexpected error code " + error + ", expected to fail with out of memory");
                    }
                    return;
                case controller.ChannelClosed():
                    throw new Exception("RamDisk client manager closed channel prematurely");
            }
        }

        private static string! CreateTest(RamDiskControlContract.Imp! controller,
                                          ulong                       diskSizeBytes)
        {
            controller.SendCreate(diskSizeBytes);

            switch receive {
                case controller.CreateSuccess(diskPath):
                    string result = Bitter.ToString2(diskPath);
                    delete diskPath;
                    return result;
                case controller.Fail(error):
                    throw new Exception("Create disk failed with error code " + error);
                case controller.ChannelClosed():
                    throw new Exception("RamDisk client manager closed channel prematurely");
            }
        }

        private static DiskDeviceContract.Imp:Ready!
        OpenDevice(DirectoryServiceContract.Imp:Ready! nsImp,
                   string!                             deviceName)
        {
            DiskDeviceContract.Exp! diskExp;
            DiskDeviceContract.Imp! diskImp;
            DiskDeviceContract.NewChannel(out diskImp, out diskExp);

            nsImp.SendBind(Bitter.FromString2(deviceName), diskExp);
            switch receive {
                case nsImp.AckBind():
                    switch receive {
                        case diskImp.Success():
                            return diskImp;
                        case diskImp.ContractNotSupported():
                            delete diskImp;
                            throw new Exception("RamDisk does not support disk contract");
                        case diskImp.ChannelClosed():
                            delete diskImp;
                            throw new Exception("RamDisk closed channel prematurely");
                    }
                    // unreached
                case nsImp.NakBind(badExp, errorCode):
                    delete diskImp;
                    delete badExp;
                    throw new Exception("Failed to bind disk '" + deviceName + "' with error code " + errorCode);
                case nsImp.ChannelClosed():
                    delete diskImp;
                    throw new Exception("Directory Service closed channel prematurely");
            }
        }

        private static void EnsureDoesNotExist(DirectoryServiceContract.Imp:Ready! nsImp,
                                               string!                             fileName)
        {
            DiskDeviceContract.Exp! fileExp;
            DiskDeviceContract.Imp! fileImp;
            DiskDeviceContract.NewChannel(out fileImp, out fileExp);

            nsImp.SendBind(Bitter.FromString2(fileName), fileExp);
            switch receive {
                case nsImp.AckBind():
                    throw new Exception("File expected to be missing exists");
                case nsImp.NakBind(badExp, errorCode):
                    delete fileImp;
                    delete badExp;
                    if (errorCode != ErrorCode.NotFound) {
                        throw new Exception("Failed to bind file '" + fileName + "' expected to be missing with unexpected error code " + errorCode);
                    }
                    return;
                case nsImp.ChannelClosed():
                    delete fileImp;
                    throw new Exception("Directory Service closed channel prematurely");
            }
        }

        private static byte[]! in ExHeap Read(DiskDeviceContract.Imp:Ready! imp,
                                              ulong                      sectorId,
                                              [Claims] byte[]! in ExHeap data)

        {
            ulong dataLength = (ulong)data.Length;
            imp.SendRead(data, 0, dataLength, sectorId);
            switch receive {
                case imp.AckRead(outBuffer):
                    return outBuffer;
                case imp.NakRead():
                    throw new Exception("RamDisk rejected read operation");
                case imp.ChannelClosed():
                    throw new Exception("RamDisk closed channel prematurely");
            }
        }

        private static byte[]! in ExHeap Write(DiskDeviceContract.Imp:Ready! imp,
                                               ulong                         sectorId,
                                               [Claims] byte[]! in ExHeap    data)
        {
            imp.SendWrite(data, 0, (ulong)data.Length, sectorId);
            switch receive {
                case imp.AckWrite(outBuffer):
                    return outBuffer;
                case imp.NakWrite():
                    throw new Exception("RamDisk rejected write operation");
                case imp.ChannelClosed():
                    throw new Exception("RamDisk closed channel prematurely");
            }
        }

        private static void EnsureDestroyFailsWithInUse(RamDiskControlContract.Imp! controller,
                                                        string!                     diskPath)
        {
            char[] in ExHeap diskPathExHeap = Bitter.FromString2(diskPath);
            controller.SendDestroy(diskPathExHeap, false/*force*/);

            switch receive {
                case controller.Success():
                    throw new Exception("Destroy disk succeeded where expected to fail with in-use error");
                case controller.Fail(errorCode):
                    if (errorCode != RamDiskContractErrorCode.IsInUse) {
                        throw new Exception("Destroy disk failed with unexpected error code " + errorCode + ", expected in-use");
                    }
                    return;
                case controller.ChannelClosed():
                    throw new Exception("RamDisk client manager closed channel prematurely");
            }
        }

        private static void Destroy(RamDiskControlContract.Imp! controller,
                                    string!                     diskPath,
                                    bool                        force)
        {
            char[] in ExHeap diskPathExHeap = Bitter.FromString2(diskPath);
            controller.SendDestroy(diskPathExHeap, force);

            switch receive {
                case controller.Success():
                    return;
                case controller.Fail(error):
                    throw new Exception("Destroy disk failed with error code " + error);
                case controller.ChannelClosed():
                    throw new Exception("RamDisk client manager closed channel prematurely");
            }
        }
    }
}


