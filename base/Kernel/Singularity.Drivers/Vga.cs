////////////////////////////////////////////////////////////////////////////////
//
//  Microsoft Research Singularity
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
//  File:   Vga.cs
//
//  Notes:
//
//  Useful reference URLs:
//      http://www.xs4all.nl/~ganswijk/chipdir/reg/vga.txt "The VGA Registers"
//      http://osdev.neopages.net/FreeVGA/vga/graphreg.htm
//

using System;

using Microsoft.Singularity.Channels;
using Microsoft.Singularity.Hal;
using Microsoft.Singularity.Io;
using Microsoft.Singularity.Configuration;

namespace Microsoft.Singularity.Drivers
{
    // create the resource object for CTR to fill in
    [DriverCategory]
    [Signature("pci/cc_0300")]
    internal class VgaResources : DriverCategoryDeclaration
    {
        [IoFixedPortRange(Base = 0x3c0, Length = 0x20, Shared = true)]
        IoPortRange dev;

        [IoFixedMemoryRange(Base = 0xa0000, Length = 0x20000, Shared = true)]
        public IoMemoryRange screenMemory;

        [IoFixedMemoryRange(Base = 0xb8000, Length = 0x8000, Shared = true)]
        public IoMemoryRange textBuffer;

        // Provide to unify creation.
        public static IDevice! DeviceCreate(IoConfig! configobj, String! instanceName)
        {
            DebugStub.Print("Creating VGA Display\n");
            return new Vga();
        }
    }

    public class Vga : ISvgaDevice
    {
        public const ushort ATC_ADDR_PORT               = 0x00;  // 3c0: Attribute Controller Address and
        public const ushort MISC_OUTPUT_REG_WRITE_PORT  = 0x02;  // 3c2: Miscellaneous Output reg write port
        public const ushort SEQ_ADDR_PORT               = 0x04;  // 3c4: Sequence Controller Address and
        public const ushort SEQ_DATA_PORT               = 0x05;  // 3c5: Data registers
        public const ushort DAC_PIXEL_MASK_PORT         = 0x06;  // 3c6: DAC pixel mask reg
        public const ushort DAC_ADDR_WRITE_PORT         = 0x08;  // 3c8: DAC register write index reg
        public const ushort DAC_DATA_REG_PORT           = 0x09;  // 3c9: DAC data transfer reg
        public const ushort GRAPH_ADDR_PORT             = 0x0e;  // 3ce: Graphics Controller Address
        public const ushort GRAPH_DATA_PORT             = 0x0f;  // 3cf: Graphics Controller Data
        public const ushort CRTC_ADDR_COLOR_PORT        = 0x14;  // 3d4: CRT Controller Address and
        public const ushort INPUT_STATUS_COLOR_PORT     = 0x1a;  // 3da: Input Status 1 register read port in color mode

        public const int SCREEN_HEIGHT = 480;
        public const int SCREEN_WIDTH = 640;

        public void BitBltPng(int x, int y, byte[] buffer)
        { /// dummy def
        }

        public Vga()
        {
            IoPortRange dev = new IoPortRange(0x3c0, 0x20, Access.ReadWrite);

            atcAddrPort = dev.PortAtOffset(ATC_ADDR_PORT, 2, Access.ReadWrite);
            miscOutputRegWritePort = dev.PortAtOffset(MISC_OUTPUT_REG_WRITE_PORT, 2, Access.ReadWrite);
            seqAddrPort = dev.PortAtOffset(SEQ_ADDR_PORT, 2, Access.Write);
            seqDataPort = dev.PortAtOffset(SEQ_DATA_PORT, 2, Access.ReadWrite);
            dacPixelMaskPort = dev.PortAtOffset(DAC_PIXEL_MASK_PORT, 2, Access.Write);
            dacAddressWritePort = dev.PortAtOffset(DAC_ADDR_WRITE_PORT, 2, Access.Write);
            dacDataRegPort = dev.PortAtOffset(DAC_DATA_REG_PORT, 2, Access.Write);
            graphAddrPort = dev.PortAtOffset(GRAPH_ADDR_PORT, 2, Access.Write);
            graphDataPort = dev.PortAtOffset(GRAPH_DATA_PORT, 2, Access.ReadWrite);
            crtcAddressColorPort = dev.PortAtOffset(CRTC_ADDR_COLOR_PORT, 2, Access.ReadWrite);
            inputStatusColorPort = dev.PortAtOffset(INPUT_STATUS_COLOR_PORT, 2, Access.ReadWrite);

            screenBuffer = IoMemory.AllocateIo(0xa0000, 0x20000, true, true);
            textBuffer = IoMemory.AllocateIo(0xb8000, 0x8000, true, true);
        }

        private HalConsole lastScreen;

        //
        // VGA register definitions
        //
        private IoPort  atcAddrPort;            // Attribute Controller Address and
        private IoPort  miscOutputRegWritePort; // Miscellaneous Output reg write port
        private IoPort  seqAddrPort;            // Sequence Controller Address and
        private IoPort  seqDataPort;            // Data registers
        private IoPort  dacPixelMaskPort;       // DAC pixel mask reg
        private IoPort  dacAddressWritePort;    // DAC register write index reg
        private IoPort  dacDataRegPort;         // DAC data transfer reg
        private IoPort  graphAddrPort;          // Graphics Controller Address
        private IoPort  graphDataPort;          // Graphics Controller Data
        private IoPort  crtcAddressColorPort;   // CRT Controller Address and
        private IoPort  inputStatusColorPort;   // Input Status 1 register read port in color mode

        private IoMemory screenBuffer;
        private IoMemory textBuffer;

        //
        // VGA indexed register indexes.
        //
        private const byte SEQ_RESET_REG        = 0;
        private const byte SEQ_CLOCK_REG        = 1;
        private const byte SEQ_PLANEMASK_REG    = 2;
        private const byte SEQ_CHARSET_REG      = 3;
        private const byte SEQ_MEMORY_REG       = 4;

        private const byte GRAPH_SET_REG        = 0;
        private const byte GRAPH_ENABLE_REG     = 1;
        private const byte GRAPH_COMPARE_REG    = 2;
        private const byte GRAPH_OPERATION_REG  = 3;
        private const byte GRAPH_READSEL_REG    = 4;
        private const byte GRAPH_MODE_REG       = 5;
        private const byte GRAPH_MISC_REG       = 6;
        private const byte GRAPH_DONTCARE_REG   = 7;
        private const byte GRAPH_BITMASK_REG    = 8;

        private const byte WRITE_MODE_0         = 0;
        private const byte WRITE_MODE_1         = 1;
        private const byte WRITE_MODE_2         = 2;
        private const byte WRITE_MODE_3         = 3;
        private const byte READ_MODE_0          = 0;
        private const byte READ_MODE_1          = 8;

        //
        // Values for Attribute Controller Index register to turn video off
        // and on, by setting bit 5 to 0 (off) or 1 (on).
        //
        private const byte VIDEO_ENABLE          = 0x20;

        private const uint BI_RLE4 = 2;

        //
        // globals to track screen position
        //

        private const int DELTA = 80;

        static private byte[] lMaskTable = new byte[8] {0xff, 0x7f, 0x3f, 0x1f, 0x0f, 0x07, 0x03, 0x01};
        static private byte[] rMaskTable = new byte[8] {0x80, 0xc0, 0xe0, 0xf0, 0xf8, 0xfc, 0xfe, 0xff};
        static private byte[] PixelMask = new byte[8] {0x80, 0x40, 0x20, 0x10, 0x08, 0x04, 0x02, 0x01};

        private void ReadWriteMode(byte mode)
        {
            graphAddrPort.Write8(GRAPH_MODE_REG);
            graphDataPort.Write8(mode);
        }

        private void Plot(int x, int y, byte color)
        {
            int offset = y * DELTA + (x / 8);

            ReadWriteMode(READ_MODE_1 | WRITE_MODE_2);
            graphAddrPort.Write8(GRAPH_BITMASK_REG);
            graphDataPort.Write8(PixelMask[x % 8]);

            // The read triggers the latch register.
            screenBuffer.Read8(offset);
            screenBuffer.Write8(offset, color);
        }

        private void Fill(int x1, int y1, int x2, int y2, byte color)
        {
            if (x1 < 0 || x1 >= SCREEN_WIDTH ||
                x2 < 0 || x2 >= SCREEN_WIDTH ||
                y1 < 0 || y1 >= SCREEN_HEIGHT ||
                y2 < 0 || y2 >= SCREEN_HEIGHT) {

                throw new OverflowException("Draw bounds invalid.");
            }

            byte lMask = lMaskTable[x1 % 8];
            byte rMask = rMaskTable[x2 % 8];

            int bank1 = x1 / 8;
            int bank2 = x2 / 8;
            int count = bank2 - bank1;

            if (count == 0) {
                lMask &= rMask;
            }

            ReadWriteMode(READ_MODE_1 | WRITE_MODE_2);

            //
            // Do the left edge
            //

            graphAddrPort.Write8(GRAPH_BITMASK_REG);
            graphDataPort.Write8(lMask);

            int pDst = y1 * DELTA + bank1;
            for (int y = y1; y <= y2; y++) {

                // The read triggers the latch register.
                screenBuffer.Read8(pDst);
                screenBuffer.Write8(pDst, color);
                pDst += DELTA;
            }

            if (count != 0) {

                //
                // Do the right edge
                //

                pDst = y1 * DELTA + bank2;
                count--;
                graphAddrPort.Write8(GRAPH_BITMASK_REG);
                graphDataPort.Write8(rMask);

                for (int y = y1; y <= y2; y++) {
                    // The read triggers the latch register.
                    screenBuffer.Read8(pDst);
                    screenBuffer.Write8(pDst, color);
                    pDst += DELTA;
                }

                //
                // Do the center section
                //

                if (count != 0) {

                    pDst = y1 * DELTA + bank1 + 1;

                    graphAddrPort.Write8(GRAPH_BITMASK_REG);
                    graphDataPort.Write8(0xff);

                    for (int y = y1; y <= y2; y++) {
                        screenBuffer.Write8(pDst, (byte)color, count);
                        pDst += DELTA;
                    }

                }
            }
        }

        private void BitBlt4(int x, int y, int width, int height,
                             byte[] buffer, int offset, int ScanWidth)
        {
            byte[] Plane = new byte [81];
            bool bRightEdge = false;
            bool bCenterSection = false;

            byte lMask = lMaskTable[x % 8];
            byte rMask = rMaskTable[(x + width - 1) % 8];

            int bank1 = x / 8;
            int bank2 = (x + width - 1) / 8;

            int count = bank2 - bank1;

            if (bank1 == bank2) {
                lMask &= rMask;
            }

            if (count != 0) {

                bRightEdge = true;

                count--;

                if (count != 0) {

                    bCenterSection = true;
                }
            }

            int pDst = (y * DELTA) + (x / 8);
            int pSrc = offset;

            ReadWriteMode(READ_MODE_0 | WRITE_MODE_0);

            for (uint j = 0; j < height; j++) {

                for (byte plane = 1; plane < 16; plane <<= 1) {

                    int pSrcTemp = pSrc;
                    int pDstTemp = pDst;

                    //
                    // Convert the packed bitmap data into planar data
                    // for this plane.
                    //

                    int bank = bank1;
                    Plane[bank] = 0;
                    byte Mask = PixelMask[x % 8];
                    uint toggle = 0;

                    for (uint i = 0; i < width; i++) {

                        if ((toggle++ & 0x1) != 0) {

                            if ((buffer[pSrcTemp] & plane) != 0) {
                                Plane[bank] |= Mask;
                            }

                            pSrcTemp++;

                        }
                        else {

                            if (((buffer[pSrcTemp] >> 4) & plane) != 0) {
                                Plane[bank] |= Mask;
                            }
                        }

                        Mask >>= 1;

                        if (Mask == 0) {
                            bank++;
                            Plane[bank] = 0;
                            Mask = 0x80;
                        }
                    }

                    //
                    // Set up the vga so that we see the correct bit plane.
                    //

                    seqAddrPort.Write8(SEQ_PLANEMASK_REG);
                    seqDataPort.Write8(plane);

                    //
                    // bank will go from bank1 to bank2
                    //

                    bank = bank1;
                    pDstTemp = pDst;


                    //
                    // Set Bitmask for left edge.
                    //
                    graphAddrPort.Write8(GRAPH_BITMASK_REG);
                    graphDataPort.Write8(lMask);

                    // The read triggers the latch register.
                    screenBuffer.Read8(pDstTemp);
                    screenBuffer.Write8(pDstTemp++, Plane[bank++]);

                    if (bCenterSection) {

                        graphAddrPort.Write8(GRAPH_BITMASK_REG);
                        graphDataPort.Write8(0xff);

                        screenBuffer.Write8(pDstTemp, Plane, bank, count);
                        bank += count;
                        pDstTemp += count;
                    }

                    if (bRightEdge) {

                        //
                        // Set bitmask for right edge.
                        //

                        graphAddrPort.Write8(GRAPH_BITMASK_REG);
                        graphDataPort.Write8(rMask);

                        // The read triggers the latch register.
                        screenBuffer.Read8(pDstTemp);
                        screenBuffer.Write8(pDstTemp, Plane[bank]);
                    }
                }

                pDst += DELTA;
                pSrc += ScanWidth;
            }

            // Restore the settings.
            seqAddrPort.Write8(SEQ_PLANEMASK_REG);
            seqDataPort.Write8(0x0f);
        }

        private void BitBlt1(int x, int y, int width, int height,
                             byte[] buffer, int offset, int ScanWidth, byte color)
        {
            int bank1 = x / 8;
            int bank2 = (x + width - 1) / 8;

            byte lMask = lMaskTable[x % 8];
            byte rMask = rMaskTable[(x + width - 1) % 8];

            if (bank1 == bank2) {
                lMask &= rMask;
            }

            int pSrc = offset;
            int pDst = (y * DELTA) + (x / 8);

            int shift = x % 8;

            ReadWriteMode(READ_MODE_0 | WRITE_MODE_0);

            graphAddrPort.Write8(GRAPH_ENABLE_REG);
            graphDataPort.Write8((byte)(color ^ 0x0f));

            for (uint j = 0; j < height; j++) {

                int pDstTemp = pDst;
                int pSrcTemp = pSrc;
                int count = width;

                //
                // non aligned case
                //

                if (shift != 0) {

                    //
                    // Left Edge.
                    //

                    graphAddrPort.Write8(GRAPH_BITMASK_REG);
                    graphDataPort.Write8(lMask);

                    // The read triggers the latch register.
                    screenBuffer.Read8(pDstTemp);
                    screenBuffer.Write8(pDstTemp++, (byte)(buffer[pSrcTemp] >> shift));

                    count -= (8 - shift);

                    //
                    // Now do center section
                    //

                    graphAddrPort.Write8(GRAPH_BITMASK_REG);
                    graphDataPort.Write8(0xff);

                    while (count > 7) {
                        screenBuffer.Write8(pDstTemp++,
                                            (byte)((buffer[pSrcTemp] << (8 - shift)) |
                                                   (buffer[pSrcTemp+1] >> shift)));

                        pSrcTemp++;
                        count -= 8;
                    }

                    //
                    // Now do the right edge.
                    //

                    if (count != 0) {

                        graphAddrPort.Write8(GRAPH_BITMASK_REG);
                        graphDataPort.Write8(rMask);

                        // The read triggers the latch register.
                        screenBuffer.Read8(pDstTemp);
                        screenBuffer.Write8(pDstTemp++,
                                            (byte)(buffer[pSrcTemp] << (8 - shift)));
                    }

                }
                else {

                    //
                    // Aligned case.
                    //
                    graphAddrPort.Write8(GRAPH_BITMASK_REG);
                    graphDataPort.Write8(0xff);

                    screenBuffer.Write8(pDstTemp, buffer, pSrcTemp, count / 8);
                    pSrcTemp += count / 8;
                    pDstTemp += count / 8;
                    count %= 8;

                    //
                    // Now do any remaining bits.
                    //

                    if (count != 0) {

                        graphAddrPort.Write8(GRAPH_BITMASK_REG);
                        graphDataPort.Write8(rMask);

                        // The read triggers the latch register.
                        screenBuffer.Read8(pDstTemp);
                        screenBuffer.Write8(pDstTemp++, buffer[pSrcTemp]);
                    }
                }

                pSrc += ScanWidth;
                pDst += DELTA;
            }

            graphAddrPort.Write8(GRAPH_ENABLE_REG);
            graphDataPort.Write8(0x00);
            graphAddrPort.Write8(GRAPH_BITMASK_REG);
            graphDataPort.Write8(0xff);
        }

        // Display a bitmap at a given location.
        public void BitBltBmp(int x, int y, byte[] buffer)
        {
            BITMAPFILEHEADER bfh;
            BITMAPINFOHEADER bih;
            int lDelta;
            int cbScanLine;
            int used;
            int offset = 0;

            bfh = BITMAPFILEHEADER.Read(buffer, offset, out used);
            bih = BITMAPINFOHEADER.Read(buffer, used, out used);

            if (bih.biWidth == 0 || bih.biHeight == 0) {
                return;
            }

            if (x < 0) {
                x = SCREEN_WIDTH + x - bih.biWidth;
            }
            if (y < 0) {
                y = SCREEN_HEIGHT + y - bih.biHeight;
            }

            if (x < 0 || x + bih.biWidth > SCREEN_WIDTH ||
                y < 0 || y + bih.biHeight > SCREEN_HEIGHT) {

                throw new OverflowException("Draw bounds invalid.");
            }

            offset = offset + bfh.bfOffBits;
            used = offset;

            //
            // Make sure this is a 1bpp or 4bpp bitmap.
            //

            if ((bih.biBitCount * bih.biPlanes) <= 4 || bih.biCompression != 0) {

                cbScanLine = (((bih.biWidth * bih.biBitCount) + 31) & ~31) / 8;

                if (bih.biHeight < 0) {

                    // top down bitmap
                    lDelta = cbScanLine;
                    bih.biHeight = -bih.biHeight;

                }
                else {

                    // bottom up bitmap
                    offset += cbScanLine * (bih.biHeight - 1);
                    lDelta = -cbScanLine;
                }

                if (used + cbScanLine * bih.biHeight > buffer.Length) {
                    DebugStub.Print("{0} + {1} * {2} = {3} > {4}\n",
                                    __arglist(
                                        used,
                                        cbScanLine,
                                        bih.biHeight,
                                        used + cbScanLine * bih.biHeight,
                                        buffer.Length);
                    throw new OverflowException("Bitmap invalid.");
                }

                if (bih.biBitCount == 1) {
                    BitBlt1(x, y, bih.biWidth, bih.biHeight, buffer, offset, lDelta, 15);
                }
                else if (bih.biBitCount == 4) {
                    BitBlt4(x, y, bih.biWidth, bih.biHeight, buffer, offset, lDelta);
                }

            }
            else {

                //
                // We don't support this type of bitmap.
                //
                DebugStub.Print("((bih.biBitCount * bih.biPlanes) not supported");
            }
        }

        public void Scroll(int x1, int y1, int x2, int y2, int CharHeight)
        {
            if (x1 < 0 || x1 >= SCREEN_WIDTH ||
                x2 < 0 || x2 >= SCREEN_WIDTH ||
                y1 < 0 || y1 >= SCREEN_HEIGHT ||
                y2 < 0 || y2 >= SCREEN_HEIGHT ||
                y2 - y1 < CharHeight) {

                throw new OverflowException("Draw bounds invalid.");
            }

            int width = (x2 / 8) - (x1 / 8) + 1;

            ReadWriteMode(READ_MODE_0 | WRITE_MODE_1);

            graphAddrPort.Write8(GRAPH_BITMASK_REG);  // enable write to all bits in plane
            graphDataPort.Write8(0xff);

            int pDst = y1 * DELTA + (x1 / 8);
            int pSrc = pDst + DELTA * CharHeight;

            for (int i = y1; i <= y2 - CharHeight; i++) {

                int pDstTemp = pDst;
                int pSrcTemp = pSrc;

                for (int j = 0; j < width; j++) {
                    // The read triggers the latch register.
                    screenBuffer.Read8(pSrcTemp++);
                    // The write triggers a write from the latch register, value ignored.
                    screenBuffer.Write8(pDstTemp++, 0);
                }

                pDst += DELTA;
                pSrc += DELTA;
            }
        }

        public void Plot(int x, int y, RGB color)
        {
            Plot(x, y, (byte)color);
        }

        public void Fill(int x1, int y1, int x2, int y2, RGB color)
        {
            Fill(x1, y1, x2, y2, (byte)color);
        }

        public void BitBltChr(int x, int y, int width, int height,
                       byte[] buffer, int offset, int ScanWidth,
                       RGB color, RGB background)
        {
            BitBlt1(x, y, width, height, buffer, offset + height - ScanWidth, -ScanWidth, (byte)color);
        }

        private void SetPaletteEntry(byte index, uint RGB)
        {
            dacAddressWritePort.Write8(index);
            dacDataRegPort.Write8((byte)(RGB & 0xff));
            dacDataRegPort.Write8((byte)((RGB >> 8) & 0xff));
            dacDataRegPort.Write8((byte)((RGB >> 16) & 0xff));
        }

        private void InitializePalette()
        {
            uint[] Palette = new uint[]
                {
                    0x00000000,
                    0x00000020,
                    0x00002000,
                    0x00002020,
                    0x00200000,
                    0x00200020,
                    0x00202000,
                    0x00202020,
                    0x00303030,
                    0x0000003f,
                    0x00003f00,
                    0x00003f3f,
                    0x003f0000,
                    0x003f003f,
                    0x003f3f00,
                    0x003f3f3f,
                };

            for (byte i = 0; i < Palette.Length; i++) {
                SetPaletteEntry(i, Palette[i]);
            }

        }

        //  This routine initializes the VGA.
        public void Initialize()
        {
            DebugStub.Print("Initializing VGA Driver\n");

            Vga640x480();
            DebugStub.Print("  VGA.AtInitialization\n");
            AtInitialization();
            DebugStub.Print("  VGA.InitializePalette\n");
            InitializePalette();

            DebugStub.Print("  VGA.Fill\n");
            Fill(0, 0, SCREEN_WIDTH-1, SCREEN_HEIGHT-1, 11);
            DebugStub.Print("  VGA.new SVGA\n");
            SvgaWindow console = new SvgaWindow(this, 0, 0, SCREEN_WIDTH-1, SCREEN_HEIGHT-1);

            lastScreen = Console.Screen;
            Console.Screen = console;

            Console.WriteLine("Singularity VGA Driver");
            Console.WriteLine();
            Console.WriteLine();
            Console.WriteLine();
        }

        public void Finalize()
        {
            if (lastScreen != null) {
                Console.Screen = lastScreen;
            }

            AtInitialization();
            InitializePalette();

            VgaTextMode();

            for (int i = 0; i < 50 * 80 * 2; i++) {
                textBuffer.Write16(i, 0x1f41);
            }
        }

        private void IndxOut(IoPort port, byte[] values)
        {
            for (ushort i = 0; i < values.Length; i++) {
                port.Write16((ushort)(i + ((ushort)values[i] << 8)));
            }
        }

        private void AtcOut(IoPort port, byte[] values)
        {
            for (byte i = 0; i < values.Length; i++) {
                port.Write8(i);
                port.Write8(values[i]);
            }
        }

        //
        private void VgaTextMode()
        {
            // start sync reset program up sequencer
            IndxOut(seqAddrPort, new byte[] { 0x01,0x00,0x03,0x00,0x02 } );

            miscOutputRegWritePort.Write8(0x67);
            graphAddrPort.Write16(0x0e06);

            //  EndSyncResetCmd
            seqAddrPort.Write16(0x0300);

            // Unlock the CTC registers.
            crtcAddressColorPort.Write16(0x0E11);

            // program crtc registers
            IndxOut(crtcAddressColorPort, new byte[] { 0x5F,0x4f,0x50,0x82,0x55,0x81,
                                                       0xbf,0x1f,0x00,0x4f,0x0d,0x0e,
                                                       0x00,0x00,0x00,0x00,0x9c,0x8e,
                                                       0x8f,0x28,0x1f,0x96,0xb9,0xa3,
                                                       0xFF } );

            // prepare atc for writing
            inputStatusColorPort.Read8();
            AtcOut(atcAddrPort, new byte[] { 0x00,0x01,0x02,0x03,0x04,0x05,0x14,0x07,
                                             0x38,0x39,0x3a,0x3b,0x3c,0x3d,0x3e,0x3f,
                                             0x04,0x00,0x0F,0x08,0x00 } );

            // program graphics controller registers
            IndxOut(graphAddrPort, new byte[] { 0x00,0x00,0x00,0x00,0x00,0x10,0x0e,0x00,0xff});

            // DAC mask registers
            dacPixelMaskPort.Write8(0xFF);

            // prepare atc for writing
            inputStatusColorPort.Read8();

            // turn video on.
            atcAddrPort.Write8(VIDEO_ENABLE);
        }

        //
        // Code to put vga into mode 12.
        //
        private void Vga640x480()
        {
            DebugStub.Print("  Vga640x480:1\n");
            // start sync reset program up sequencer
            seqAddrPort.Write8(SEQ_RESET_REG);
            seqDataPort.Write8(0);
            seqAddrPort.Write8(SEQ_CLOCK_REG);
            seqDataPort.Write8(0x01);
            seqAddrPort.Write8(SEQ_PLANEMASK_REG);
            seqDataPort.Write8(0x0f);
            seqAddrPort.Write8(SEQ_CHARSET_REG);
            seqDataPort.Write8(0x00);
            seqAddrPort.Write8(SEQ_MEMORY_REG);
            seqDataPort.Write8(0x06);

            DebugStub.Print("  Vga640x480:2\n");
            miscOutputRegWritePort.Write8(0xe3);

            DebugStub.Print("  Vga640x480:3\n");
            // Set chain mode in sync reset
            graphAddrPort.Write8(GRAPH_MISC_REG);
            graphDataPort.Write8(0x05); // graphics and 64KB buffer

            DebugStub.Print("  Vga640x480:4\n");
            // EndSyncResetCmd
            seqAddrPort.Write8(SEQ_RESET_REG);
            seqDataPort.Write8(0x03);

            DebugStub.Print("  Vga640x480:5\n");
            // Unlock CRTC registers 0-7
            crtcAddressColorPort.Write16(0x0511);

            DebugStub.Print("  Vga640x480:6\n");
            // program crtc registers
            IndxOut(crtcAddressColorPort, new byte[] { 0x5F,0x4F,0x50,0x82,0x54,0x80,
                                                       0x0B,0x3E,0x00,0x40,0x00,0x00,
                                                       0x00,0x00,0x00,0x00,0xEA,0x8C,
                                                       0xDF,0x28,0x00,0xE7,0x04,0xE3,
                                                       0xFF } );

            // prepare atc for writing
            inputStatusColorPort.Read8();

            DebugStub.Print("  Vga640x480:7\n");
            // program attribute controller registers
            AtcOut(atcAddrPort, new byte[] { 0x00,0x01,0x02,0x03,0x04,0x05,0x06,0x07,
                                             0x08,0x09,0x0a,0x0b,0x0c,0x0d,0x0e,0x0f,
                                             0x01,0x00,0x0F,0x00,0x00 } );

            DebugStub.Print("  Vga640x480:8\n");
            // program graphics controller registers
            graphAddrPort.Write8(GRAPH_SET_REG);
            graphDataPort.Write8(0x00);
            graphAddrPort.Write8(GRAPH_ENABLE_REG);
            graphDataPort.Write8(0x00);
            graphAddrPort.Write8(GRAPH_COMPARE_REG);
            graphDataPort.Write8(0x00);
            graphAddrPort.Write8(GRAPH_OPERATION_REG);
            graphDataPort.Write8(0x00);
            graphAddrPort.Write8(GRAPH_READSEL_REG);
            graphDataPort.Write8(0x00);
            graphAddrPort.Write8(GRAPH_MODE_REG);
            graphDataPort.Write8(0x00);
            graphAddrPort.Write8(GRAPH_MISC_REG);
            graphDataPort.Write8(0x05);
            graphAddrPort.Write8(GRAPH_DONTCARE_REG);
            graphDataPort.Write8(0x00); // was 0x0f
            graphAddrPort.Write8(GRAPH_BITMASK_REG);
            graphDataPort.Write8(0xff);

            DebugStub.Print("  Vga640x480:9\n");
            // DAC mask registers
            dacPixelMaskPort.Write8(0xFF);

            DebugStub.Print("  Vga640x480:10\n");
            // prepare atc for writing
            inputStatusColorPort.Read8();

            DebugStub.Print("  Vga640x480:11\n");
            // turn video on.
            atcAddrPort.Write8(VIDEO_ENABLE);
        }


        //
        // Initialize AT registers
        //
        private void AtInitialization()
        {
            // prepare atc for writing
            inputStatusColorPort.Read8();

            // program attribute controller registers
            AtcOut(atcAddrPort, new byte[] { 0x00,0x01,0x02,0x03,0x04,0x05,0x06,0x07,
                                             0x08,0x09,0x0a,0x0b,0x0c,0x0d,0x0e,0x0f
            });

            // prepare atc for writing
            inputStatusColorPort.Read8();

            // turn video on.
            atcAddrPort.Write8(VIDEO_ENABLE);
        }
    }
}

