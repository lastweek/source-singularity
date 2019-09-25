///////////////////////////////////////////////////////////////////////////////
//
//  Microsoft Research Singularity
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
//  File:   TPM.cs
//
//  Note:
//
//  Useful refs:

//

//#define DEBUG_DISPATCH_IO
//#define DEBUG_IO


using Microsoft.Singularity.Io;

using System;
using System.Runtime.CompilerServices;
using System.Diagnostics;
using System.Threading;

using Microsoft.Singularity.Configuration;

namespace Microsoft.Singularity.Hal
{

    // create the resource object for LTR to fill in
    [DriverCategory]
    [Signature("/pseudobus0/tpm12")]
    public sealed class TpmResources : DriverCategoryDeclaration
    {
        [IoMemoryRange(1, Default = 0xfed40000, Length = 0x4000)]
        public IoMemoryRange pcrs;
    }


    //////////////////////////////////////////////////////////////////////////
    //
    //  Underlying device implementation.
    //
    internal class Tpm
    {
        private class TpmRegisterOffsets
        {
            public const int TpmRegAccess = 0x0;
            public const int TpmStatus = 0x18;
            public const int TpmBurst = 0x19;
            public const int TpmDataFifo = 0x24;
        };

        private class TpmRegAccessMasks
        {
            public const byte TpmAccessValidStatus  = 0x80;
            public const byte TpmAccessActiveLocality  = 0x20;
            public const byte TpmAccessHasBeenSeized = 0x10;
            public const byte TpmAccessRequestUse = 0x2;
        };

        private class TpmRegStatusMasks
        {
            public const byte TpmStatusValid = 0x80;
            public const byte TpmStatusCommandReady = 0x40;
            public const byte TpmStatusGo = 0x20;
            public const byte TpmStatusDataAvailable = 0x10;
            public const byte TpmStatusExpect = 0x8;
            public const byte TpmStatusRetry = 0x2;

        };

        // Retries assuming 1 ms wait between retry
        //
        // TODO: those are the default values, grab the actual ones from the device

        private class Retries
        {
            public const int MaxStatusRetries = 200;
            public const int MaxDataRetries = 400;

        }

        byte[] capability_command = {0, 193,
                                     0, 0, 0, 18,
                                     0, 0, 0, 101,
                                     0, 0, 0, 6,
                                     0, 0, 0, 0 };

        private int locality = 0;

        private IoMemory tpmIoMemory;

        private byte[] minResponse;

        //private const int minResponseLen = 6;
        private const int minResponseLen = 6;
        private const int dataLenOffset = 2;


        // Constructor
        internal Tpm(/*TpmResources! res*/)
        {
            Tracing.Log(Tracing.Debug, "Tpm: Initialize() called\n");

            DebugStub.WriteLine("Tpm: Initialize() called");

            tpmIoMemory = IoMemory.MapPhysicalMemory(new UIntPtr(0xfed40000),
                                                  new UIntPtr(0x4000),
                                                  true,
                                                  true);

            if (tpmIoMemory == null) {
                DebugStub.WriteLine("Tpm: Initialize(), MapPhysicalMemory failed");

            }

            minResponse = new byte[minResponseLen];



        }

        internal void PrintRegisters()
        {
            byte TpmAccess = tpmIoMemory.Read8(locality + TpmRegisterOffsets.TpmRegAccess);
            byte TpmStatus = tpmIoMemory.Read8(locality + TpmRegisterOffsets.TpmStatus);

            DebugStub.WriteLine("Tpm: PrintRegisters() Access={0:x2}, Status={1:x2}", __arglist(TpmAccess, TpmStatus));


        }

        ushort GetBurst()
        {
            ushort burst = 0;
            for (int j = 0; j < Retries.MaxDataRetries; j++) {
                burst = tpmIoMemory.Read16(locality + TpmRegisterOffsets.TpmBurst);

                if (burst != 0)
                    break;

                Thread.Sleep(1);
            }

            return burst;


        }

        //byte Read8(int byteOffset)

        internal bool WaitOnBit(int address, byte mask, int MaxRetries)
        {
            for (int i = 0; i < MaxRetries; i++) {
                byte data = tpmIoMemory.Read8(address);

                if ((data & mask) > 0)
                    return true;

                Thread.Sleep(1);
            }
            return false;

        }

        internal bool Send(byte[] command)
        {
            bool Status = true;

            DebugStub.WriteLine("Tpm: Send() called");
            PrintRegisters();


            byte TpmAccess = tpmIoMemory.Read8(locality + TpmRegisterOffsets.TpmRegAccess);


            //
            // check the access register
            //

            //
            // check if the TPM has been disabled
            //

            if (TpmAccess == 0xff) {
                DebugStub.WriteLine("Tpm: Send() TPM disabled");
                return false;
            }

            if ((TpmAccess & TpmRegAccessMasks.TpmAccessHasBeenSeized) > 0) {
                DebugStub.WriteLine("Tpm: Send() TPM seized");
                return false;
            }

            if ((TpmAccess & TpmRegAccessMasks.TpmAccessValidStatus) == 0) {
                DebugStub.WriteLine("Tpm: Send() TPM had invalid status");
                return false;
            }


            //
            // request locality use
            //

            if ((TpmAccess & TpmRegAccessMasks.TpmAccessActiveLocality) == 0) {
                //
                TpmAccess |= TpmRegAccessMasks.TpmAccessActiveLocality;
                tpmIoMemory.Write8(locality + TpmRegisterOffsets.TpmRegAccess, TpmAccess);

                if (!WaitOnBit(locality + TpmRegisterOffsets.TpmRegAccess,
                               TpmRegAccessMasks.TpmAccessActiveLocality,
                               Retries.MaxStatusRetries))
                {
                    DebugStub.WriteLine("Tpm: Send() could not set locality");
                    return false;

                }

            }

            //
            // check if the device is ready
            //

            byte TpmStatus = tpmIoMemory.Read8(locality + TpmRegisterOffsets.TpmStatus);

            if ((TpmStatus & TpmRegStatusMasks.TpmStatusCommandReady) == 0) {
                TpmStatus |= TpmRegStatusMasks.TpmStatusCommandReady;
                tpmIoMemory.Write8(locality + TpmRegisterOffsets.TpmStatus, TpmStatus);

                if (!WaitOnBit(locality + TpmRegisterOffsets.TpmStatus,
                               TpmRegStatusMasks.TpmStatusCommandReady,
                               Retries.MaxStatusRetries))
                {
                    DebugStub.WriteLine("Tpm: Send() device not ready");
                    PrintRegisters();
                    return false;

                }

            }

            DebugStub.WriteLine("Tpm: Send() command length={0:x2}", __arglist(command.Length));

            //
            // write the data to the data register
            //

            for (int i = 0; i < command.Length;) {
                ushort burst = 0;

                burst = GetBurst();

                if (burst == 0) {
                    DebugStub.WriteLine("Tpm: Send() timed out waiting for burst");
                    return false;
                }

                while (burst > 0) {
                    burst--;

                    if (i == command.Length)
                        break;

                    //
                    // last byte, check if we still expect
                    //

                    if (i == command.Length - 1) {
                        TpmStatus = tpmIoMemory.Read8(locality + TpmRegisterOffsets.TpmStatus);

                        if ((TpmStatus & TpmRegStatusMasks.TpmStatusExpect) == 0) {
                            //
                            // something went wrong
                            //
                            DebugStub.WriteLine("Tpm: Send() not expecting more data before last byte");
                            return false;

                        }
                        DebugStub.WriteLine("Tpm: Send() last byte expected ok");

                    }

                    tpmIoMemory.Write8(locality + TpmRegisterOffsets.TpmDataFifo, command[i]);


                    i++;

                }


            }

            if (!WaitOnBit(locality + TpmRegisterOffsets.TpmStatus,
                           TpmRegStatusMasks.TpmStatusValid,
                           Retries.MaxDataRetries))
            {
                DebugStub.WriteLine("Tpm: Send(), WaitOnTpmStatusValid timed out after command write");
                PrintRegisters();
                return false;

            }

            TpmStatus = tpmIoMemory.Read8(locality + TpmRegisterOffsets.TpmStatus);

            if ((TpmStatus & TpmRegStatusMasks.TpmStatusExpect) > 0) {
                //
                // more data needed
                //
                DebugStub.WriteLine("Tpm: Send(), more data needed");
                return false;

            }


            //
            // launch the command
            //
            TpmStatus |= TpmRegStatusMasks.TpmStatusGo;
            tpmIoMemory.Write8(locality + TpmRegisterOffsets.TpmStatus, TpmStatus);

            DebugStub.WriteLine("Tpm: Send(), success");

            return Status;

        }

        private bool ReadBytes(byte[] buffer, int offset, int numBytes, ushort prevBurst, out ushort burstRemainder)
        {
            byte TpmStatus;
            burstRemainder = 0;
            //
            // read the remaining burst bytes
            //


            if (prevBurst > 0) {
                for (int i = 0; i < prevBurst; i++) {
                   if (numBytes > 0) {
                       TpmStatus = tpmIoMemory.Read8(locality + TpmRegisterOffsets.TpmStatus);

                       if ((TpmStatus & TpmRegStatusMasks.TpmStatusDataAvailable) == 0) {
                           DebugStub.WriteLine("Tpm: ReadBytes() no more data avaliable, ={0:d4}", __arglist(numBytes));
                           return false;
                       }


                   }

                   if (numBytes <= 0)
                        return true;


                    buffer[offset] = tpmIoMemory.Read8(locality + TpmRegisterOffsets.TpmDataFifo);
                    offset++;
                    numBytes--;
                }
            }

            ushort burst = 0;

            while (numBytes > 0) {
                //get next burst

                burst = GetBurst();

                if (burst == 0) {
                    DebugStub.WriteLine("Tpm: ReadBytes() timed out waiting for burst");
                    return false;
                }

                while (burst > 0) {
                    burst--;
                    if (numBytes == 1) {
                        TpmStatus = tpmIoMemory.Read8(locality + TpmRegisterOffsets.TpmStatus);
                        if ((TpmStatus & TpmRegStatusMasks.TpmStatusDataAvailable) == 0) {
                            DebugStub.WriteLine("Tpm: ReadBytes() no more data avaliable2");
                            return false;
                        }
                    }

                    buffer[offset] = tpmIoMemory.Read8(locality + TpmRegisterOffsets.TpmDataFifo);
                    offset++;
                    numBytes--;

                    if (numBytes == 0) {
                        burstRemainder = burst;
                        return true;
                    }


                }


            }
            return false;

        }

        bool ReceiveAttempt(out byte[] response)
        {
            bool Ready = false;
            bool DataAvailable = false;
            bool Status = true;
            response = null;
            byte TpmStatus;

            DebugStub.WriteLine("Tpm: ReceiveAttempt() called");

            for (int i = 0; i < Retries.MaxDataRetries; i++) {
                if (WaitOnBit(locality + TpmRegisterOffsets.TpmStatus,
                   TpmRegStatusMasks.TpmStatusValid,
                   Retries.MaxDataRetries))
                {
                    Ready = true;

                }
            }

            if (!Ready) {
                DebugStub.WriteLine("Tpm: ReceiveAttempt() device not ready");
                return false;
            }

            for (int i = 0; i < Retries.MaxDataRetries; i++) {

                TpmStatus = tpmIoMemory.Read8(locality + TpmRegisterOffsets.TpmStatus);

                if ((TpmStatus & TpmRegStatusMasks.TpmStatusDataAvailable) > 0) {
                    DataAvailable = true;
                    break;

                }
                Thread.Sleep(1);
            }

            if (!DataAvailable) {
                DebugStub.WriteLine("Tpm: ReceiveAttempt(), data not available");
                return false;

            }

            //
            // read enough bytes to determine the length
            //

            ushort burstRemainder;

            Status = ReadBytes(minResponse, 0, minResponseLen, 0, out burstRemainder);

            if (!Status) {
                DebugStub.WriteLine("Tpm: ReceiveAttempt(), ReadBytes failed");
                return false;
            }

            int dataLen = 0;

            //
            // acquire data length
            //

            dataLen = (minResponse[dataLenOffset] << 24) | (minResponse[dataLenOffset + 1] << 16) |
                      (minResponse[dataLenOffset + 2] << 8) | (minResponse[dataLenOffset + 3]);

            DebugStub.WriteLine("Tpm: ReceiveAttempt() data length={0:d4}", __arglist(dataLen));

            response = new byte[dataLen];

            for (int i = 0; i < minResponseLen; i++) {
                response[i] = minResponse[i];

            }

            ushort nextBurstRem;


            Status = ReadBytes(response, minResponseLen, dataLen - minResponseLen, burstRemainder, out nextBurstRem);

            if (!Status) {
                DebugStub.WriteLine("Tpm: ReceiveAttempt(), ReadBytes failed2");
                return false;
            }


            if (!WaitOnBit(locality + TpmRegisterOffsets.TpmStatus,
               TpmRegStatusMasks.TpmStatusValid,
               Retries.MaxDataRetries))
            {
                DebugStub.WriteLine("Tpm: ReceiveAttempt(), valid bit not set after done reading");
                //PrintRegisters();
                return false;

            }

            return Status;



        }


        bool Receive(out byte[] response)
        {
            bool Status;
            response = null;

            for (int i = 0; i < Retries.MaxDataRetries; i++) {
                Status = ReceiveAttempt(out response);
                if (Status)
                    return Status;

                byte TpmStatus = tpmIoMemory.Read8(locality + TpmRegisterOffsets.TpmStatus);
                TpmStatus |= TpmRegStatusMasks.TpmStatusRetry;
                tpmIoMemory.Write8(locality + TpmRegisterOffsets.TpmStatus, TpmStatus);
                Thread.Sleep(10);

            }

            return false;


        }

        internal bool SendReceive(byte[] request, out byte[] response)
        {
            bool Status;

            response = null;

            Status = Send(request);
            if (!Status)
                return Status;

            Status = Receive(out response);

            if (Status) {
                DebugStub.WriteLine("Tpm: SendReceive(), success");

            }

            return Status;

        }

        // Device methods
        public void Initialize()
        {

        }
//
//      ///////////////////////////////////////////////////////////////////////
//      //
//      // Register accessors / modifiers / utilities
//      //
//
//      private uint Read(uint offset)
//      {
//          return ioMemory.Read32((int) offset);
//      }
//
//      private void Write(uint offset, uint value)
//      {
//          ioMemory.Write32((int) offset, value);
//      }
//
//      private void SetBits(int offset, uint bits)
//      {
//          ioMemory.Write32(offset, ioMemory.Read32(offset) | bits);
//      }
//
//      private void ClearBits(int offset, uint bits)
//      {
//          ioMemory.Write32(offset, ioMemory.Read32(offset) & ~bits);
//      }
//

        public void ReleaseResources()
        {
            Tracing.Log(Tracing.Debug, "Tpm: Finalize() called\n");
        }

        // how do we pass a string back?

        public string Name
        {
            get { return "TPM 1.2 compliant device"; }
        }

        public string Version
        {
            get { return "0.1"; }
        }

    }
}
