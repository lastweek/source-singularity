////////////////////////////////////////////////////////////////////////////////
//
//  Microsoft Research Singularity
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
//  File:   BusMasterDma.cs
//
// See "Programming Interface for Bus Master IDE Controller"
// or  www.t13.org  1510D Draft "ATA/ATAPI Host Adapters Standard(ATA - Adapter)"

//
//  1. Software prepares a PRD Table in host memory.
//  2. Software provides the starting address of the PRD Table by loading the PRD Table
//          Pointer Register.
//      Setting of the Read/Write Control bit specifies the direction of the data transfer.
//      Clearing the Interrupt and Error bits in the ATA Bus Master Status register
//          to zero readies the adapter for a data transfer.
//  3. Software issues the appropriate DMA transfer command to the device.
//  4. Software initiates the bus master function by writing a one to the Start bit
//      in the ATA Bus Master Command Register for the appropriate channel.
//  5. The adapter transfers data to/from host memory responding to DMA requests from the ATA device.`
//

//#define DEBUG_BUS_MASTER_DMA

using System;
using System.Text;
using System.Threading;
using System.Runtime.CompilerServices;  //StructAlign attribute
using System.Runtime.InteropServices;   //structLayout attribute
using Microsoft.SingSharp;
using Microsoft.Singularity;
using Microsoft.Singularity.Io;
using Microsoft.Singularity.Drivers.IDE;
using Microsoft.Singularity.V1.Services;

namespace Microsoft.Singularity.Drivers.IDE
{
    [CLSCompliant(false)]
    public class BusMasterDma
    {
        enum BmState
        {
            BmIdle = 0,
            BmPrepared ,
            BmArmed,
            BmDisarmed,
        }

        public const int PRD_BYTES_PER_ENTRY = 8;
        public const int PRD_ALIGNMENT       = 4096;
        public const int PRD_MAX_ENTRIES     = 4096 / PRD_BYTES_PER_ENTRY;

        // BusMaster Status Bits
        private const byte BUSMASTER_STATUS_MASK_DEVICE1_DMA_OK     =   0x40;
        private const byte BUSMASTER_STATUS_MASK_DEVICE0_DMA_OK     =   0x20;
        private const byte BUSMASTER_STATUS_MASK_INTERRUPT          =   0x04;
        private const byte BUSMASTER_STATUS_MASK_ERROR              =   0x02;
        private const byte BUSMASTER_STATUS_MASK_ACTIVE             =   0x01;

        //BusMaster Control bits
        private const byte BUSMASTER_CONTROL_MASK_WRITE             = 0x08;
        private const byte BUSMASTER_CONTROL_MASK_START             = 0x01;
        private const byte BUSMASTER_CONTROL_MASK_STOP              = 0x00;

        private IoPort commandPort;
        private IoPort statusPort;
        private IoPort prdPort;
        private IoMemory prdRegion;

        private IdeConfig ideConfigHandle;
        private bool runningVPC;

        private BmState busMasterState;   // the state we think the BusMaster it is in

        const byte PrdTableTerminate = 0x80;

        public  BusMasterDma(IdeConfig! ideConfig)
        {
            ideConfigHandle = ideConfig;

            // Set up BusMaster ports for this controller
            // <command, status, PRD table>
            commandPort = ideConfig.DmaBase.PortAtOffset(0, 1, Access.ReadWrite);
            statusPort  = ideConfig.DmaBase.PortAtOffset(2, 1, Access.ReadWrite);
            prdPort     = ideConfig.DmaBase.PortAtOffset(4, 4, Access.ReadWrite);
            // PRD needs to be 4-byte aligned and within one 4k page.
            prdRegion   =
                IoMemory.AllocatePhysical(PRD_MAX_ENTRIES * PRD_BYTES_PER_ENTRY,
                                          PRD_ALIGNMENT);
        } // BusMasterInitialize

        public void Uninitialize ()
        {
            commandPort = null; //???
        }

        public void Setup ()
        {
        }

        public void BmPrepareController (IdeRequest! ideRequest)
        {
            // Perform steps 1 and 2 above: set up PRD, clear
            // error snd interrupt

            // Init. Scatter Gather List Register
            uint thePrd = FillPrdTable(ideRequest);
            prdPort.Write32(thePrd);

            // Clear Errors
            byte status = (byte) (BUSMASTER_STATUS_MASK_INTERRUPT | BUSMASTER_STATUS_MASK_ERROR);
            statusPort.Write8(status);

            return;
        } // BmPrepareController

        public void SetVirtualized()
        {
            runningVPC = true;
            return;
        }

        public int Arm (IdeRequest! ideRequest)
        {
            byte value = BUSMASTER_CONTROL_MASK_START;

            if (ideRequest.Command == IdeCmdType.Read) {
                value |=  BUSMASTER_CONTROL_MASK_WRITE;
            }
            commandPort.Write8(value);  // enable BM
            return 0;
        } // BmArm

        public byte GetStatus()
        {
            byte status = statusPort.Read8();
            return status;
        }

        public bool InterruptHigh()
        {
            //probe the status register to see if we have been interrupted
            byte status = statusPort.Read8();
            if ((status & (byte) BUSMASTER_STATUS_MASK_INTERRUPT) == 0) {
                return false;
            }
            return true;

        }
        public void Disarm ()
        {
            //According to the "Programming Interface for Bus Master IDE Controller"
            // 1) reset the Start/Stop bit in command register
            // 2) read controller status
            // 3) read drive status
            //  to determine if the xfer completed successfully.

            commandPort.Write8(BUSMASTER_CONTROL_MASK_STOP);  // disable BM
            //Tracing.Log(Tracing.Debug," stop: fullstatus ={0:x}\n",(UIntPtr)ideConfigHandle.IdeController.ReadFullStatus());
            byte status = GetStatus();
            if ((status & (byte)BUSMASTER_STATUS_MASK_INTERRUPT) == 0) {
                Tracing.Log(Tracing.Debug,"BusMaster.Disarm: interrupt line not set {0}!\n",(UIntPtr) status);
                DebugStub.WriteLine("BusMaster.Disarm: interrupt line not set {0}!\n",__arglist(status));
                //DebugStub.Break();
            }

            if ((status & (byte)BUSMASTER_STATUS_MASK_ERROR) > 0) {
                Tracing.Log(Tracing.Debug,"BusMaster.Disarm: error!!!!\n",(UIntPtr) status);
                DebugStub.WriteLine("BusMaster.Disarm: error!!!!\n",__arglist(status));
                //DebugStub.Break();
            }

            status = (byte) (BUSMASTER_STATUS_MASK_INTERRUPT | BUSMASTER_STATUS_MASK_ERROR);
            statusPort.Write8( status);  // clear interrupt BM

            //Tracing.Log(Tracing.Debug,"cntlr status   ={0:x}\n",(UIntPtr)ideConfigHandle.IdeController.ReadFullStatus());
            //Tracing.Log(Tracing.Debug,"bm status : {0:x}",(UIntPtr) statusPort.Read8());
        } // BmDisarm

        [ System.Diagnostics.Conditional("DEBUG_BUS_MASTER_DMA") ]
        public void DumpPrd()
        {
            for (int i = 0; i < PRD_MAX_ENTRIES; i++) {
                uint address;
                uint length;
                bool eot;

                ReadPrdEntry(i, out address, out length, out eot);
                Tracing.Log(Tracing.Debug,
                            "prd[{0}]: {1:x8} {2:x4}\n",
                            (UIntPtr) i,
                            (UIntPtr) address,
                            (UIntPtr) length);
                if (eot) {
                    Tracing.Log(Tracing.Debug, "prd[{0}]: EOT\n", (UIntPtr) i);
                    break;
                }
            }
        }

        private uint FillPrdTable(IdeRequest! ideRequest)
        {
            // given a memory address and a length generate
            // a Physical Region Descriptor Table (PDRT) to be used
            // in a IDE busmaster DMA transfer

            //a PRDT table is an array of PRD entries, each 8 bytes in
            //length. There is no count associated with this structure
            // Bit 7 of the last byte of the last entry signifies the
            //end of the table

            // PRD (Physical Region Descriptor)
            // the first 4 bytes of a PRD specify the memory address
            // Bytes 5 and 6 (16 bits) specify the length.
            // At most a PRD can specify a transfer of 64KB.
            // The memory specified by a PRD cannot cross a 64KB boundary
            // Any transfer that would cross such a boundary needs to be
            // split into to separate PRDs

            uint addr = (uint)((UIntPtr)ideRequest.BufferAddress + ideRequest.BufferOffset);
            uint len  = (uint)ideRequest.Length;

            // Write a bad entry at the end
            WritePrdEntry(PRD_MAX_ENTRIES - 1, 0, 0xbad1, true);

            uint baseAddr = addr;
            uint bytesToMap = len;
            int i = 0;
            while (0 != bytesToMap) {
                uint did = WritePrdChunk(i, baseAddr, bytesToMap);
                baseAddr   += did;
                bytesToMap -= did;
                i++;
            }

            // DEBUG CHECK
            uint computedLen = 0 ;
            bool eotFound   = false;
            for (i = 0; i < PRD_MAX_ENTRIES; i++) {
                uint dummy;
                uint length;
                bool eot;
                ReadPrdEntry(i, out dummy, out length, out eot);
                computedLen = computedLen + length;
                if (eot) {
                    eotFound = true;
                    break;
                }
            }

            if (computedLen != len || !eotFound) {
                throw new ApplicationException("PRD length mismatch");
            }
            DumpPrd();

            return (uint) prdRegion.PhysicalAddress.Value;
        }

        private UIntPtr Get64KLimit(UIntPtr a)
        {
            const uint count = 0x10000;
            return (a.ToUInt32() + count) & ~(count - 1u);
        }

        // Write a descriptor for up to 64K of user data.  Write stops on
        // 64K boundaries or discontinuity in physical memory.
        //
        // Returns the number of bytes written into PRD.
        private uint WritePrdChunk(int     prdIndex,
                                   UIntPtr baseVA,
                                   uint    baseVALength)
        {
            UIntPtr basePA;
            UIntPtr bytesOnPage;

            if (!DeviceService.GetDmaPhysicalAddress(baseVA,
                                                     out basePA,
                                                     out bytesOnPage)) {
                throw new ApplicationException(
                    "Bad physical address translation"
                    );
            }

            UIntPtr basePALimit = Get64KLimit(basePA);
            if (basePALimit > basePA + baseVALength) {
                basePALimit = basePA + baseVALength;
            }

            UIntPtr expectedPA = basePA + bytesOnPage;
            baseVA += bytesOnPage;
            while (expectedPA < basePALimit) {
                UIntPtr currentPA;
                if (!DeviceService.GetDmaPhysicalAddress(baseVA,
                                                         out currentPA,
                                                         out bytesOnPage)) {
                    throw new ApplicationException(
                        "Bad physical address translation"
                        );
                }
                if (currentPA != expectedPA) {
                    // Physical page discontinuity
                    break;
                }
                expectedPA = currentPA + bytesOnPage;
                baseVA     = baseVA + bytesOnPage;
            }

            if (expectedPA < basePALimit) {
                basePALimit = expectedPA;
            }

            uint done = (basePALimit - basePA).ToUInt32();

            WritePrdEntry(prdIndex,
                          basePA.ToUInt32(),
                          (ushort) (done & 0xffff),
                          done == baseVALength);

            return done;
        }

        private void
        WritePrdEntry(int  index,
                      uint addr,
                      uint length,
                      bool endOfTable)
            requires length != 0 && length <= 0x10000;
        {
            // PRD structure in octets:
            // - 0:3 baseAddress
            // - 4:5 length
            // - 6:6 reserved
            // - 7:7 end of table
            int baseOffset = index * PRD_BYTES_PER_ENTRY;
            this.prdRegion.Write32(baseOffset,
                                   ByteOrder.HostToLittleEndian(addr));
            ushort slen = (ushort)(length & 0xffffu); // 0 == 64K
            this.prdRegion.Write16(baseOffset + 4,
                                   ByteOrder.HostToLittleEndian(slen));
            this.prdRegion.Write8(baseOffset + 7,
                                  endOfTable ? PrdTableTerminate : (byte)0);
        }

        private void
        ReadPrdEntry(int      index,
                     out uint addr,
                     out uint length,
                     out bool endOfTable)
        {
            int baseOffset = index * PRD_BYTES_PER_ENTRY;
            addr = ByteOrder.LittleEndianToHost(
                this.prdRegion.Read32(baseOffset)
                );
            ushort slen = ByteOrder.LittleEndianToHost(
                this.prdRegion.Read16(baseOffset + 4)
                );
            length = (slen == 0) ? 0x10000u : (uint)slen;
            byte end   = this.prdRegion.Read8(baseOffset + 7);
            endOfTable = (end == PrdTableTerminate);
        }
    } // BusMaster Class
}//namespace
