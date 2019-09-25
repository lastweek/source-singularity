////////////////////////////////////////////////////////////////////////////////
//
//  Microsoft Research Singularity
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
//  File:   S3Trio64.cs
//
//  Note:
//

using Microsoft.Singularity;

using System;
using System;
using System.Text;
using System.Configuration.Assemblies;
using System.Runtime.Remoting;
using System.Runtime.InteropServices;
using System.Collections;

namespace Microsoft.Singularity.Drivers
{
        public void BitBltPng(int x, int y, byte[] buffer)
        {
            if (!Ready) {
                return;
            }

            //Png.Png.DisplayPngImage(x,y,buffer,lineBuffer);
            Png obj=new Png();
            obj.chunk_list= new Hashtable();
            ArrayList idat_list = new ArrayList();
            CHUNK chunk;
            obj.buffer = buffer;
            obj.ptr=0;
            if (!obj.chksignature()) {
                throw new Exception("Invalid Signature");
            }

            // step 1 : chk signature
            // look for header
            while (obj.ptr < obj.buffer.Length) {
                chunk = new CHUNK();
                chunk.init_CHUNK(obj.buffer, ref obj.ptr,out obj.tp);
                switch (obj.tp) {
                    case TYPE.IHDR:
                        cIHDR ihdr = new cIHDR(chunk,x,y);
                        obj.scanlength = ihdr.scanlength;
                        obj.bpp= ihdr.bpp;
                        // do some error checking

                        if (ihdr.width == 0 || ihdr.height == 0) {
                            return;
                        }

                        if (x < 0) {
                            ihdr.x = (int)(ActiveMode.ScreenWidth + x - ihdr.width);
                        }
                        if (y < 0) {
                            ihdr.y = (int)(ActiveMode.ScreenHeight + y - ihdr.height);
                        }

                        if (ihdr.x < 0 || ihdr.x + ihdr.width > ActiveMode.ScreenWidth ||
                            ihdr.y < 0 || ihdr.y + ihdr.height > ActiveMode.ScreenHeight)
                        {

                            throw new OverflowException("Draw bounds invalid.");
                        }
                        obj.chunk_list.Add("IHDR",ihdr);
                        break;
                    case TYPE.bKGD:// define later
                        break;
                    case TYPE.cHRM:
                        break;
                    case TYPE.gAMA:
                        cgAMA gama = new cgAMA(chunk);
                        obj.chunk_list.Add("gAMA",gama);
                        break;
                    case TYPE.hIST:
                        break;
                    case TYPE.iCCP:
                        break;
                    case TYPE.IDAT:cIDAT idat = new cIDAT(chunk);
                        idat_list.Add(idat);
                        if (!obj.chunk_list.ContainsKey("IDAT")) {
                            obj.chunk_list.Add("IDAT",idat_list);
                        }
//                        DebugStub.Print("Chkpoint 1");
//                        try
//                        {
//                            obj.chunk_list.Add("IDAT",idat_list);
//                            DebugStub.Print("Chkpoint 1");
//                        }
//                        catch(System.ArgumentException)
//                        {// do nothing
//                            DebugStub.Break();
//                        }
                        break;
                    case TYPE.IEND:
                        cIEND iend= new cIEND(chunk);
                        obj.chunk_list.Add("IEND",iend);
                        break;
                    case TYPE.iTXt:
                        break;
                    case TYPE.meTa:
                        break;
                    case TYPE.pHYs:
                        break;
                    case TYPE.PLTE:
                        break;
                    case TYPE.sBIT:
                        break;
                    case TYPE.sPLT:
                        break;
                    case TYPE.sRGB:
                        break;
                    case TYPE.tEXt:
                        break;
                    case TYPE.tIME:
                        break;
                    case TYPE.tRNS:
                        break;
                    case TYPE.zTXt:
                        break;
                    default:throw new Exception("Invalid chunk type");

                }
            }
            try {
                obj.buffer=((cIDAT)((ArrayList)obj.chunk_list["IDAT"])[0]).decompressandfilter(obj.scanlength,obj.bpp,idat_list);
            }
                //decompress it
                //defilter it

            catch (Exception e) {
                DebugStub.Print("message from exception {0} {1}.\n",
                                __arglist(e.Message, e));// to be removed later
                DebugStub.Print(" IDAT CHUNK MISSING");
                throw new Exception(" IDAT CHUNK MISSING or Corrupt");
            }
            try {
                byte[] correctedbuffer; // buffer after gamma correction
                //add later ((cgAMA)obj.chunk_list[TYPE.gAMA]).gammacorrection(obj.buffer,out correctedbuffer);
                // add later    obj.buffer=correctedbuffer;
                //gamma correction
            }
            catch (Exception) {
                // Do nothing as ancilliary chunk
            }
//            DebugStub.Break();
//            for (long i=0;i<obj.buffer.Length;i++)
//                DebugStub.Print("{0:x} ", __arglist(obj.buffer[i]));
            try {
                Display.display(obj.buffer,obj.chunk_list,lineBuffer,screenBuffer,ActiveMode);
                //display
            }
            catch (Exception e) {
                DebugStub.Print("Exception {0} {1}", __arglist(e.Message, e));
                DebugStub.Print("IHDR CHUNK MISSING");
            }
//            DebugStub.Print("Exitting");
//            DebugStub.Break();
            // end
        }

    enum FILTER_METHOD:byte{ADAPTIVE_FILTER};
    enum COMPRESSION_METHOD:byte{DEFLATE_INFLATE};
    enum COLOR_TYPE:byte{GRAY_SCALE=0,RGBTRIPLATE=2,PALETTEINDEX=3,GRAYSCALE_ALPHA=4,RGB_ALPHA=6};
    enum INTERLACE_METHOD:byte{NO_INTERLACE,ADAM7};
    enum CHUNK_TYPE:byte{ANCILLARY,CRITICAL};
    enum TYPE:uint
    {
        IHDR=0x49484452,
        PLTE=0x504c5445,
        IDAT=0x49444154,
        IEND=0x49454e44,
        tRNS=0x74524e53,
        gAMA=0x67414d41,
        cHRM=0x6348524d,
        sRGB=0x73524742,
        iCCP=0x69434350,
        iTXt=0x69545874,
        tEXt=0x74455874,
        zTXt=0x7A545874,
        bKGD=0x624b4744,
        pHYs=0x70485973,
        sPLT=0x73504c54,
        sBIT=0x73424954,
        hIST=0x68495354,
        tIME=0x74494d45,
        meTa=0x6d655461
    };
    enum FILTER_TYPE:byte{NONE,SUB,UP,AVERAGE,PAETH};
    enum FILTER_OPERATION:byte{ENCODE,DECODE};

    public class Buffer
    {
        public byte[] buf;
        public int startptr;
        public int length;
        public Buffer(byte[] buffer , int startpointer , int len)
        {
            buf= buffer;
            startptr = startpointer;
            length = len;
        }
    }

    class cIHDR : CHUNK
    {
        public int x;
        public int y;
        public uint width;          // width of image in pixels: 0 not valid
        public uint height;     // height of image in pixels: 0 not valid
        public byte bit_depth;      // no of bits per sample or per palette index
        public byte sample_depth;   // not present in the IHDR but initialized depending on data present in it
        public COLOR_TYPE color_type;   // describes the interpretion of image data
        COMPRESSION_METHOD compression_method;  // compression method
        FILTER_METHOD filter_method;            // filter method
        INTERLACE_METHOD interlace_method;      // transmission order of the image
        public uint scanlength;
        public byte bpp;

        public cIHDR(CHUNK obj,int x,int y):base(obj)
        {
            this.x = x;
            this.y =y;
            color_type=COLOR_TYPE.GRAY_SCALE;
            compression_method=COMPRESSION_METHOD.DEFLATE_INFLATE;
            filter_method = FILTER_METHOD.ADAPTIVE_FILTER;
            interlace_method=INTERLACE_METHOD.NO_INTERLACE;
            init();
        }
        public void init( ) // throws an exception if this chunk found invalid or corrupt
        {
            uint ptr=(uint)data.startptr;
            uint startindex=ptr;
            try {
                width=(256*256*256*(uint)data.buf[ptr++]+256*256*(uint)data.buf[ptr++]
                    +256*(uint)data.buf[ptr++]+(uint)data.buf[ptr++]);
                height=256*256*256*(uint)data.buf[ptr++]+256*256*(uint)data.buf[ptr++]
                    +256*(uint)data.buf[ptr++]+(uint)data.buf[ptr++];
                bit_depth=data.buf[ptr++];
                color_type=(COLOR_TYPE)(data.buf[ptr++]);
//                DebugStub.Print("color_type : {0} data.buf[ptr-1]:{1}",__arglist((int)color_type,data.buf[ptr-1]));
//                DebugStub.Break();

                compression_method=(COMPRESSION_METHOD)(data.buf[ptr++]);
                filter_method=(FILTER_METHOD)(data.buf[ptr++]);
                interlace_method=(INTERLACE_METHOD)(data.buf[ptr++]);
                if (color_type == COLOR_TYPE.PALETTEINDEX)sample_depth = 3; // setting sample_depth
                else sample_depth = bit_depth;
            }
            catch (Exception) // if any exception then invalid header
            {
                throw new Exception("invalid IHDR");
            }
            if ((ptr - length) != startindex)   //if incorrect length then invalid header
                throw new Exception("invalid IHDR");
            switch (bit_depth) {
                case 1:if (color_type!=COLOR_TYPE.GRAY_SCALE && color_type!=COLOR_TYPE.PALETTEINDEX)
                           throw new Exception("invalid IHDR");
                    break;
                case 2:if (color_type!=COLOR_TYPE.GRAY_SCALE && color_type!=COLOR_TYPE.PALETTEINDEX)
                           throw new Exception("invalid IHDR");
                    break;
                case 4:if (color_type!=COLOR_TYPE.GRAY_SCALE && color_type!=COLOR_TYPE.PALETTEINDEX)
                           throw new Exception("invalid IHDR");
                    break;
                case 8:if (color_type!=COLOR_TYPE.GRAY_SCALE && color_type!=COLOR_TYPE.PALETTEINDEX
                           && color_type!=COLOR_TYPE.RGB_ALPHA && color_type!=COLOR_TYPE.GRAYSCALE_ALPHA && color_type!=COLOR_TYPE.RGBTRIPLATE)
                           throw new Exception("invalid IHDR");
                    break;
                case 16:if (color_type!=COLOR_TYPE.GRAY_SCALE && color_type!=COLOR_TYPE.RGB_ALPHA
                            && color_type!=COLOR_TYPE.GRAYSCALE_ALPHA && color_type!=COLOR_TYPE.RGBTRIPLATE)
                            throw new Exception("invalid IHDR");
                    break;
                default:throw new Exception("invalid IHDR");
            }
            switch (color_type) {
                case COLOR_TYPE.GRAY_SCALE:bpp=(byte)((bit_depth%8==0)?bit_depth/8:bit_depth/8+1);break;
                case COLOR_TYPE.GRAYSCALE_ALPHA:bpp=(byte)(((bit_depth%8==0)?bit_depth/8:bit_depth/8+1)+1);break;
                case COLOR_TYPE.PALETTEINDEX:bpp=(byte)(((bit_depth*3)%8==0)?(bit_depth*3/8):(bit_depth*3)/8+1);break;
                case COLOR_TYPE.RGBTRIPLATE:bpp=(byte)(((bit_depth*3)%8==0)?(bit_depth*3/8):(bit_depth*3)/8+1);break;
                case COLOR_TYPE.RGB_ALPHA:bpp=(byte)((((bit_depth*3)%8==0)?(bit_depth*3/8):(bit_depth*3)/8+1)+1);break;
                default : throw new Exception("Invalid color type");
            }
            scanlength= width * bpp + 1; // 1 for the filter type
        }
    }// end of class cIHDR

    class cgAMA:CHUNK
    {
        uint gamma;         // stores gamma times 100000
        public cgAMA(CHUNK obj):base(obj)
        {
            gamma = 100000;
            init();

        }
        public void init( ) // throws an exception if this chunk found invalid or corrupt
        {
            uint ptr=(uint)data.startptr;
            uint startindex=ptr;
            try {
                gamma=(256*256*256*(uint)data.buf[ptr++]+256*256*(uint)data.buf[ptr++] +256*(uint)data.buf[ptr++]+(uint)data.buf[ptr++]);
            }
                // it won't throw any exception since its an ancilliary chunk but if
                // length is invalid then it will throw an exception
            catch (IndexOutOfRangeException) // if index out of range then invalid header
            {
                throw new Exception("invalid gAMA");
            }
            if ((ptr - length) != startindex)   //if incorrect length then invalid header
                throw new Exception("invalid gAMA");
        }
        public void gammacorrection(byte[] srcbuf,out byte[] dstbuf)
        {
            dstbuf = new byte[10];
        }
        private byte gammacorrection(byte integer_sample)
        {
            //      double sample = integer_sample/((2<<bitdepth)- 1.0);
            //      display_output = pow(sample,(1.0/gamma));
            //      display_input = inverse_display_transfer(display_output);
            //      framebuf_sample = (byte)(display_input * MAX_FRAMEBUF_SAMPLE);
            //      return framebuf_sample;
            return integer_sample;
        }
        private ushort gammacorrection(ushort integer_sample)
        {
            //          sample = integer_sample/(pow(2,bitdepth)- 1.0);
            //          display_output = pow(sample,(1.0/gamma));
            //          display_input = inverse_display_transfer(display_output);
            //          framebuf_sample = ROUND(display_input * MAX_FRAMEBUF_SAMPLE);
            //          return framebuf_sample;
            return integer_sample;
        }
    }// end of class cgAMA

    class cIDAT:CHUNK
    {
        public cIDAT(CHUNK obj):base(obj)
        {
            init();
        }
        public void init( ) // throws an exception if this chunk found invalid or corrupt
        {
            if (data.length!=length) throw new Exception("Invalid IHDR chunk");
        }
        public byte[] decompressandfilter(uint scanlength,byte bpp,ArrayList idat_list)
        {
            byte[] decompressedbuffer;
            // combine data buffers of all the cIDAT objects in ArrayList idat_list
            MemoryStream ms = new MemoryStream();
            foreach (cIDAT idat in idat_list) {
                ms.Write(idat.data.buf,idat.data.startptr,idat.data.length);
            }

            //idat_list = null;
            Decompress.decompress(ms,out decompressedbuffer);
           // ms = null;
            byte[] defilteredbuffer;
             FILTER.decode(decompressedbuffer,out defilteredbuffer,scanlength,bpp);
//            DebugStub.Break();
//            for (long i=0;i<decompressedbuffer.Length;i++)
//                DebugStub.Print("{0:x} ", __argist(decompressedbuffer[i]));
             return defilteredbuffer;
        }

    }// end of class cIDAT
    class cIEND:CHUNK
    {
        public cIEND(CHUNK obj):base(obj)
        {
            init();

        }
        public void init( ) // throws an exception if this chunk found invalid or corrupt
        {
            if (length != 0) throw new Exception("invalid IEND");
            //            if (data.length!=startindex)   //if incorrect length then invalid header
            //                throw new Exception("invalid IEND");
        }
    }// end of class cIEND
    // type of recognised chunks
    class CRC
    {
        static uint[] crc_table=new uint [256];           // CRC table
        static ulong CRC_POLY=0xedb88320;     // CRC polynomial
        static bool crc_table_computed=false; // flag to indicate that CRC table is not yet made
        private static void make_crc_table()  // make CRC table so that future calculations are done faster
        {

            ulong c;
            for (uint i = 0; i < 256; i++) {
                c=(ulong)i;
                for (int j = 0; j < 8; j++) {
                    if ((c & 1) != 0)
                        c=CRC_POLY^ (c>>1);
                    else
                        c=c>>1;
                }
                crc_table[i]=(uint)c;
            }
            crc_table_computed=true;
        }

        private static uint calculateCRC(uint crc,byte[] buf,uint start_index,uint end_index)  // calculate CRC
        {
            if (!crc_table_computed)
                make_crc_table();
            for (uint i = start_index; i < end_index; i++) {
                crc = crc_table[(crc^buf[i]) & 0xff]^(crc>>8);
            }
            return crc;
        }
        public static uint getCRC(byte[] buf,uint start_index,uint end_index)       // return CRC
        {
            return (calculateCRC(0xffffffff,buf,start_index, end_index)^0xffffffff);
        }
    }

    class CHUNK:CRC
    {
        protected uint length;
        protected uint type;
        protected Buffer data;
        protected uint crc;
        protected CHUNK_TYPE chunk_type;
        public CHUNK(){}
        public CHUNK(CHUNK obj)
        {
            length= obj.length;
            type = obj.type;
            data = obj.data;
            crc = obj.crc;
            chunk_type= obj.chunk_type;
        }
        public void init_CHUNK(byte[] buffer, ref uint ptr,out TYPE t)// throws an exception if chunk invalid
        {

            uint startindex=ptr;
            uint calculatedCRC;
            try {
                length = (256*256*256*(uint)buffer[ptr++]+256*256*(uint)buffer[ptr++]
                    +256*(uint)buffer[ptr++]+(uint)buffer[ptr++]);
                calculatedCRC = getCRC(buffer, ptr, ptr + 4 + length);
                type = (uint)buffer[ptr++]*256*256*256+(uint)buffer[ptr++]*256*256+((uint)buffer[ptr++]*256)+(uint)buffer[ptr++];
                t=(TYPE)type;
                chunk_type = ((type & 0x20000000)==0)?CHUNK_TYPE.CRITICAL:CHUNK_TYPE.ANCILLARY;
                // if bit 5 of first bye of type is 1 then its ancillary otherwise essential
                if (buffer.Length<(startindex+length))throw new Exception("invalid CHUNK");
                data = new Buffer(buffer,(int)ptr,(int)length);
                ptr += length;
                //data = new byte[length];
                //for (int i = 0; i < length; i++)
                //  data[i]=buffer[ptr++];  
                crc=(256*256*256*(uint)buffer[ptr++]+256*256*(uint)buffer[ptr++]
                    +256*(uint)buffer[ptr++]+(uint)buffer[ptr++]);
            }
            catch (Exception e) // any exception indicates that the chunk is invalid
            {
                DebugStub.Print("message from exception {0} {1}",
                                __arglist(e.Message, e));// to be removed later
                throw new Exception("invalid CHUNK");
            }
            if (crc != calculatedCRC) {
                DebugStub.Print("CRC chk failed in chunk {0}\ncalculated CRC: {1:x}\n actual CRC : {2:x}",__arglist(t,calculatedCRC,crc));
//                Console.Write("start:");
//                for (int i=0;i<data.length;i++)
//                    Console.Write("{0:x}",data.buf[data.startptr + i]);
//                Console.Write(":end");
                throw new Exception("CRC chk failed");
            }
        }
    }

    delegate  void defilter();

    class FILTER
    {
        static byte[] sbuf;
        static uint scanlength;
        //delegate void screenmode(out S3_VIDEO_MODES ModeEntry);
        static byte bpp;
        public static void encode(byte[] srcbuf,out byte[] dstbuf,uint slength)
        {
            // encode the inp buffer to form the output buffer
            dstbuf = new byte[10];
        }
        public static void decode(byte[] srcbuf,out byte[] dstbuf,uint slength,byte b)
        {
            sbuf = srcbuf;
            scanlength= slength;
            bpp =b;
            //  if (srcbuf.Length % scanlength !=0) throw new Exception("Invalid buffer after decoding");
            // the buffer length should be divisible by the scanlength
            uint ptr=0;
            byte t; // no filter to start with
            while (ptr < srcbuf.Length) {
                t=srcbuf[ptr++];
                switch (t) {
                    case 0:None(ref ptr);break;
                    case 1:sub(ref ptr);break;
                    case 2:up(ref ptr);break;
                    case 3:average(ref ptr);break;
                    case 4:paeth(ref ptr);break;
                    default:
                    {
                        DebugStub.Print("Invalid filter type at byte offset : {0} in decompressed buffer : byte read: {1}",
                                        __arglist(ptr,t));
                        throw new Exception("Invalid Filter Type");// invalid filter type
                    }
                }

            }
            dstbuf = srcbuf;

        }
        private static void None(ref uint ptr)
        {
            ptr += scanlength-1;  // scan length includes the byte for filter type as well
        }
        private static void sub(ref uint ptr)
        {
            for (int i = bpp; i <(scanlength - 1); i++)
                //note the loop starting from 1 and not 0: ptr will be 1 inside this loop
                sbuf[ptr + i]=(byte)(sbuf[ptr + i]+ sbuf[ptr + i -bpp]);
            ptr +=scanlength-1;
        }
        private static void up(ref uint ptr)
        {
            if (ptr >= scanlength)// thats is for 2nd onwards line
                for (int i = 0; i <(scanlength - 1); i++)
                    sbuf[ptr + i]=(byte)(sbuf[ptr + i]+sbuf[ptr + i -scanlength]);
            ptr +=scanlength-1;
        }
        private static void average(ref uint ptr)
        {
            if (ptr >= scanlength)// thats is for 2nd onwards line
            {
                for (int i = 0; i < bpp; i++)
                    sbuf[ptr]=(byte)(sbuf[ptr]+(sbuf[ptr-scanlength]/2)); // truncate the other part
                for (int i = bpp; i <(scanlength - 1); i++)
                    sbuf[ptr + i]=(byte)(sbuf[ptr + i]+(sbuf[ptr + i -scanlength]+sbuf[ptr+i-bpp])/2);
            }
            else  // first row
            {
                for (int i = bpp; i <(scanlength - 1); i++)
                    sbuf[ptr + i]=(byte)(sbuf[ptr + i]+(byte)(sbuf[ptr+i-bpp]/2));
            }
            ptr +=scanlength-1;
        }
        private static void paeth(ref uint ptr)
        {
            // two cases :
            // 1:first row
            if (ptr < scanlength)// first row
            {
                for (uint i = 0; i < bpp; i++)
                    sbuf[ptr+i]=(byte)(sbuf[ptr+i] + paethpredictor(0,0,0));
                for (uint i = bpp; i <(scanlength - 1); i++)
                    sbuf[ptr+i]=(byte)(sbuf[ptr+i] + paethpredictor(sbuf[ptr+i-bpp],0,0));
            }
            else    // not the first row
            {
                for (uint i = 0; i < bpp; i++)
                    sbuf[ptr+i]=(byte)(sbuf[ptr+i] + paethpredictor(0x00,sbuf[ptr+i-scanlength],0x00));
                for (uint i = bpp; i <(scanlength - 1); i++)
                    sbuf[ptr+i]=(byte)(sbuf[ptr+i] + paethpredictor(sbuf[ptr+i-bpp],sbuf[ptr+i-scanlength],sbuf[ptr+i-scanlength-bpp]));
            }
            ptr +=scanlength-1;
        }
        private static byte paethpredictor(byte a , byte b , byte c)
        {
            int p  =  a + b -c;
            int pa = ((p-a)>0)?p-a:a-p;
            int pb = ((p-b)>0)?p-b:b-p;
            int pc = ((p-c)>0)?p-c:c-p;
            if ((pa <= pb) && (pa <= pc))return a;
            else if (pb <= pc) return b;
            else return c;
        }
    } // end of Filter class
    class Display
    {
        private static byte[] buffer;
        private static ushort[] linebuffer; // reference to the linebuffer of Singularity namespace
        private static COLOR_TYPE ctype;
        private static IoMemory screenBuffer;
        private static  S3_VIDEO_MODE ActiveMode;
        private static cIHDR ihdr;
        public static void display(byte[] buf,Hashtable ht,ushort[] lineBuffer,IoMemory sbuf, S3_VIDEO_MODE actmode)
        {
            buffer=buf;
            screenBuffer = sbuf;
            ActiveMode = actmode;
            linebuffer = lineBuffer;
            ihdr = (cIHDR)ht["IHDR"];
            DebugStub.Print("ihdr :{0} ", __arglist(hdr.width));
            DebugStub.Print("ihdr :{0} ", __arglist(ihdr.color_type));
            DebugStub.Print("ihdr :{0} ", __arglist(COLOR_TYPE.RGBTRIPLATE));
            switch (ihdr.color_type) {
                case COLOR_TYPE.GRAY_SCALE:showGRAY_SCALE();break;
                case COLOR_TYPE.RGBTRIPLATE:showRGBTRIPLATE();break;
                case COLOR_TYPE.PALETTEINDEX:showPALETTEINDEX();break;
                case COLOR_TYPE.GRAYSCALE_ALPHA: showGRAYSCALE_ALPHA();break;
                case COLOR_TYPE.RGB_ALPHA:showRGBALPHA();break;
                default : throw new Exception("Invalid color type");
            }

        }
        private static void showGRAY_SCALE()
        {// fill in later
        showRGBALPHA();
        }

        static ushort abc(byte red,byte green,byte blue)
        {
            return (ushort)((((ushort)red >> 3) << 11) |
                (((ushort)green >> 2) << 5) |
                ((ushort)blue >> 3));
        }

        private static void showRGBTRIPLATE()
        {

            int pDst = (int)(/*(ihdr.y + ihdr.height - 1) * ActiveMode.ScreenStride + */ihdr.x * ActiveMode.BytesPerPixel);
            linebuffer = new ushort[ihdr.width];

            for (int j = 0; j < ihdr.height; j++) {
                for (int i = 0; i < ihdr.width; i++) {
                    linebuffer[i] = RGB.Compute16(buffer[i*ihdr.bpp+1+j*ihdr.scanlength],buffer[i*ihdr.bpp+2+j*ihdr.scanlength],buffer[i*ihdr.bpp+3+j*ihdr.scanlength]);
                   // DebugStub.Print("{0} ",
                    __arglist(abc(buffer[i*ihdr.bpp+1+j*ihdr.scanlength],buffer[i*ihdr.bpp+2+j*ihdr.scanlength],buffer[i*ihdr.bpp+3+j*ihdr.scanlength])));
                }
                //DebugStub.Print("\n");
                screenBuffer.Write16(pDst, linebuffer, 0,(int)ihdr.width);

                pDst += ActiveMode.ScreenStride;
            }
        }
        private static void showPALETTEINDEX()
        {

        }
        private static void showGRAYSCALE_ALPHA()
        {
        }
        private static void showRGBALPHA()
        {
            //PictureBox pictureBox = new PictureBox();
            int pDst = (int)(/*(ihdr.y + ihdr.height - 1) * ActiveMode.ScreenStride + */ihdr.x * ActiveMode.BytesPerPixel);

            for (int j = 0; j < ihdr.height; j++) {
                for (int i = 0; i < ihdr.width; i++) {
                    linebuffer[i] = RGB.Compute16(/*buffer[x*ihdr.bpp+4+y*ihdr.scanlength],*/buffer[i*ihdr.bpp+1+j*ihdr.scanlength],buffer[i*ihdr.bpp+2+j*ihdr.scanlength],buffer[i*ihdr.bpp+3+j*ihdr.scanlength]);
                }
                screenBuffer.Write16(pDst, linebuffer, 0,(int)ihdr.width);

                pDst += ActiveMode.ScreenStride;
            }


        }
    }

    class Png
    {
        public Hashtable chunk_list;
        public byte[] SIGNATURE=new byte[]{0x89,0x50,0x4e,0x47,0x0d,0x0a,0x1a,0x0a}; // signature of PNG files
        public byte[] buffer;
        public uint ptr;
        public TYPE tp;
        public byte bpp;
        public uint scanlength;
        public bool chksignature()
        {
            // chk if first 9 bytes of the file matches the signature
            // if yes then return true else return false
            for (int i = 0; i < 8; i++)
                if (buffer[ptr++]!=SIGNATURE[i]) return false;
            return true;

        }

    }

    public class Block
    {
        public enum BTYPE:byte{NO_COMPRESSION,FIXED_HUFFMAN,DYNAMIC_HUFFMAN};
        public bool last; // is this the last block: true: yes false : no
        public BTYPE Btype;
        public byte[] buf;
        public int count; // the length of uncompressed block
    }

    public class treenode
    {
        public uint len;
        public uint code;
        public uint val;
        public treenode(uint len)
        {
            this.len = len;
        }
    }
    public class searchtree
    {

        public Hashtable ht;
        public uint MAX_BITS = 0;
        public uint MIN_BITS = 0;

        public searchtree(treenode[] t,uint[] bt_count)
        {
            uint min = t[0].len;
            uint max = t[0].len;
            for (uint i = 0; i < t.Length; i++) {
                if (min == 0)
                    min = t[i].len;
                else if (t[i].len < min && t[i].len != 0)
                    min = t[i].len; // find minimum non zero
                if (t[i].len > max)
                    max = t[i].len; // find maximun
            }
            this.MAX_BITS = max;
            this.MIN_BITS = min;
            this.setsearchtree(t,0,(uint)t.Length,bt_count);
        }

        public searchtree  (treenode[] t,uint start_index,uint end_index)
        {
            uint min = t[start_index].len;
            uint max = t[start_index].len;

            for (uint i = start_index; i < end_index; i++) {
                if (min == 0)min = t[i].len;
                else if (t[i].len < min && t[i].len != 0)min = t[i].len; // find minimum non zero
                if (t[i].len > max)max = t[i].len; // find maximun
            }
            this.MAX_BITS = max;
            this.MIN_BITS = min;
            uint[] bt_count = new uint[MAX_BITS+1];

            for (uint n = start_index; n < end_index; n++) {
                bt_count[t[n].len]++; // no of codes having bit count as this

            }
            this.setsearchtree(t,start_index,end_index,bt_count);
        }

        void setsearchtree(treenode[] t,uint start_index,uint end_index,uint[] bt_count)
        {
            uint code=0;
            ht = new Hashtable();
            bt_count[0]=0;

            uint[] next_code= new uint[16];// no code larger than 16 bits
            for (uint bits = 1; bits <= MAX_BITS; bits++) {
                code =((code + bt_count[bits-1])<<1);
                next_code[bits]=code;
            }
            for (uint n = start_index; n < end_index; n++) {
                if (t[n].len != 0) {
                    t[n].code = next_code[t[n].len]++;
                    t[n].val=n-start_index;
                    ht.Add(t[n].code,t[n]);
                    //  DebugStub.Print("{0} {1} {2}", __arglist(t[n].code, t[n].len, n));
                }
            }
        }

        public uint decode(byte[] buf, ref ulong ptr)
        {
            // return the appropriate symbol after searching from the treenode
            // throw an exception if not found
            byte bits_read= (byte)MIN_BITS; // start from reading the min no of bits
            uint val = Compressed.readnbithuffmancode(buf, ref ptr, bits_read);

            while (bits_read < MAX_BITS) {
                if (ht.ContainsKey(val)) {
                    treenode obj = (treenode)ht[val];
                    if (obj.len == (uint)bits_read) {
                        return obj.val;
                    }
                }
                else {
                    val = (val << 1) | Compressed.readbit(buf, ref ptr);
                    bits_read++;
                }
            }
            DebugStub.Print("Huffman code at ptr :{0}", __arglist(ptr));
            throw new Exception("Invalid Huffman Code");
        }
    }

    public class Compressed
    {
        uint read_fixed_huffman_val(byte[] buf, ref ulong ptr)
        {
            uint val = readnbithuffmancode(buf, ref ptr, 7);
            if (val <= 0x17)  // chk for 7 bit code
                return (256+val);
            // else read one more bit
            val = (val << 1) | readbit(buf, ref ptr);  // valid for huffman code but not otherwise
            if (val >= 0x30 && val <= 0xBF) // chk for 8 bit code
                return (val-0x30);
            if (val >= 0xc0 && val <= 0xc7)
                return(280+val-0xc0);
            val = (val << 1) + readbit(buf, ref ptr);
            if (val >= 0x190 && val <= 0x1ff) // finally it must be a 9 bit code
                return (144+val-0x190);
            throw new Exception("invalid format of file");
        }

        uint read_length(byte[] buf, ref ulong ptr, uint val)
        {
            // since length is also written as huffman codes so same method will be valid but not valid generally
            if (val >= 257) {
                if (val <= 264) {   // chk for 0 extra bit length
                    return (3 + val-257);
                }
                else if (val <= 268) {  // chk for 1 extra bit length
                    return (11 + ((val-265)<<1) + readbit(buf, ref ptr));
                }
                else if (val <= 272) {  // chk for 2 extra bit length
                    return (19 + ((val-269)<<2) + readnbit(buf, ref ptr, 2));
                }
                else if (val <= 276) {  // chk for 3 extra bit length
                    return (35 + ((val-273)<<3) + readnbit(buf, ref ptr, 3));
                }
                else if (val <= 280) {  // chk for 4 extra bit length
                    return (67 + ((val-277)<<4) + readnbit(buf, ref ptr, 4));
                }
                else if (val <= 284) {  // chk for 5 extra bit length
                    return (131 + ((val-281)<<5) + readnbit(buf, ref ptr, 5));
                }
                else if (val == 285) {
                    return 258;
                }
            }
            throw new Exception("invalid format of file");
        }

        uint read_dist(byte[] buf, ref ulong ptr, uint val)
        {
            if (val <= 3) { // chk for 0 extra bit length
                return (val+1);
            }
            else if (val <= 5) { // chk for 1 extra bit length
                return (5 + ((val-4)<<1) + readbit(buf, ref ptr));
            }
            else if (val <= 7) { // chk for 2 extra bit length
                return (9 + ((val-6)<<2) +  readnbit(buf, ref ptr, 2));
            }
            else if (val <= 9) { // chk for 3 extra bit length
                return (17 + ((val-8)<<3) + readnbit(buf, ref ptr,3 ));
            }
            else if (val <= 11) {   // chk for 4 extra bit length
                return (33 + ((val-10)<<4) + readnbit(buf, ref ptr, 4));
            }
            else if (val <= 13) {   // chk for 5 extra bit length
                return (65 + ((val-12)<<5) + readnbit(buf, ref ptr, 5));
            }
            else if (val <= 15) {   // chk for 6 extra bit length
                return (129 + ((val-14)<<6) + readnbit(buf, ref ptr, 6));
            }
            else if (val <= 17) {   // chk for 7 extra bit length
                return (257 + ((val-16)<<7) + readnbit(buf, ref ptr, 7));
            }
            else if (val <= 19) {   // chk for 8 extra bit length
                return (513 + ((val-18)<<8) + readnbit(buf, ref ptr, 8));
            }
            else if (val <= 21) {   // chk for 9 extra bit length
                return (1025 + ((val-20)<<9) + readnbit(buf, ref ptr, 9));
            }
            else if (val <= 23) {   // chk for 10 extra bit length
                return (2049 + ((val-22)<<10) + readnbit(buf, ref ptr, 10));
            }
            else if (val <= 25) {   // chk for 11 extra bit length
                return (4097 + ((val-24)<<11) + readnbit(buf, ref ptr, 11));
            }
            else if (val <= 27) {   // chk for 12 extra bit length
                return (8193 + ((val-26)<<12) + readnbit(buf, ref ptr, 12));
            }
            else if (val <= 29) {   // chk for 13 extra bit length
                return (16385 + ((val-28)<<13) + readnbit(buf, ref ptr, 13));
            }
            else {
                DebugStub.Print(" ptr : {0} | val: {1}", __arglist(ptr, val));
                throw new Exception("invalid format of file");
            }
        }

        // function to read a bit from the buffer
        public static uint readbit(byte[] buf, ref ulong ptr)
        {
            uint b = ((((uint)buf[ptr/8]) >> (int)((ptr%8))) & (1));
            ptr++;
            return b;
        }

        // function to read n bits from the buffer
        public static uint readnbit(byte[] buf, ref ulong ptr, byte n)
        {
            uint val = 0;
            for (int i = 0; i < n; i++) {
                val |= readbit(buf, ref ptr) << i;
            }
            return val;
        }

        // function to read n bits from the buffer
        public static uint readnbithuffmancode(byte[] buf, ref ulong ptr, byte n)
        {
            uint val=0;
            for (; n > 0; n--) {
                val = ((val << 1) | readbit(buf, ref ptr));
            }
            return val;
        }

        public class circularbuffer
        {
            const uint SIZE = 32768;
            uint size;//current size
            byte[] buf ;
            uint ptr;// to start with
            public circularbuffer()
            {
                ptr=0;
                size=0;
                buf = new byte[SIZE];
                if (buf==null)throw new Exception("IoMemory can't be allocated");
            }
            public byte getindexeddata(uint relative_position)  // with respect to the current ptr:behind
            {
                if (relative_position>size) throw new Exception("out of bounds parameter");
                uint pos= (ptr + SIZE - relative_position)%SIZE;
                return buf[pos];
            }
            public void writeindexeddata(byte data)  // write can only take place at the current position
            {
                if (SIZE > size) size++;
                buf[ptr]= data;
                ptr = (ptr + 1)%SIZE;
            }

        }
        ArrayList BlkList;

        public Compressed(byte[] buf, ref ulong ptr)
        {
            // ptr th bit is being referred
            BlkList= new ArrayList();
            Block blk;
            circularbuffer circ_buf = new circularbuffer();
            uint length;
            MemoryStream ms;
            BinaryWriter bw;
            treenode[] code_length_length;
            treenode[] code_length;

            do
            {
                blk = new Block();
                ms = new MemoryStream();
                bw = new BinaryWriter(ms);
                blk.last = (readbit(buf, ref ptr) != 0);// for MSB ptr%8=0
                uint btype = readnbit(buf, ref ptr, 2);
                switch (btype)// note that readnbithuffmancode is not used
                {
                    case 0:blk.Btype = Block.BTYPE.NO_COMPRESSION;break;
                    case 1:blk.Btype = Block.BTYPE.FIXED_HUFFMAN;break;
                    case 2:blk.Btype = Block.BTYPE.DYNAMIC_HUFFMAN;break;
                    default:throw new Exception("Error in block type");
                }

                switch (blk.Btype) {
                    case Block.BTYPE.NO_COMPRESSION:
                        // skip remaining bits in currently partially read byte
                        ptr -= ptr%8;
                        ptr +=8;

                        uint LEN = readnbit(buf, ref ptr, 16);
                        // uint NLEN = readnbit(buf, ref ptr, 16);
                        // to be removed later
                        //                      if ((LEN + NLEN )!=0xffff) // chk if one's complement
                        //                          throw new Exception("Error in Block");
                        length = 0;
                        blk.buf = new byte[LEN];

                        for (length = 0; length < LEN; length++) // copy length character from the buffer
                        {
                            byte readbyte = buf[ptr/8];
                            ptr += 8;
                            bw.Write(readbyte);
                            circ_buf.writeindexeddata(readbyte);
                        }
                        blk.buf=ms.GetBuffer();
                        break;
                    case Block.BTYPE.FIXED_HUFFMAN:
                        uint val;

                        //                      BinaryReader br = new BinaryReader(ms);
                        while ((val = read_fixed_huffman_val(buf, ref ptr)) != 256) {
                            // loop till end character found
                            if (val < 256) // literal
                            {

                                bw.Write((byte)val);
                            }
                            else // length - distance pair
                            {
                                length = read_length(buf, ref ptr,val);
                                val = readnbit(buf, ref ptr, 5);
                                uint distance = read_dist(buf, ref ptr,val);
                                for (uint i = 0; i < length; i++) // copy length character from the buffer
                                {

                                    byte readbyte = circ_buf.getindexeddata(distance);
                                    bw.Write(readbyte);
                                    circ_buf.writeindexeddata(readbyte);

                                }
                            }
                        }
                        // transfer buffer to blk.buf
                        blk.buf=ms.GetBuffer();
                        break;

                    case Block.BTYPE.DYNAMIC_HUFFMAN:
                        uint chkcount =0;
                        int[] border = new int[] {    // Order of the bit length code lengths   
                                                     16, 17, 18, 0, 8, 7, 9, 6, 10, 5, 11, 4, 12, 3, 13, 2, 14, 1, 15};

                    {
                        uint HLIT = (257 + readnbit(buf, ref ptr, 5));
                        uint HDIST = (1 + readnbit(buf, ref ptr, 5));
                        uint HCLEN = (4 + readnbit(buf, ref ptr, 4));

                        searchtree code_length_length_tree;
                        // block 1 :to allocate code_length_length
                        int i;
                        code_length_length = new treenode[19];

                        uint[] bt_count = new uint[8]{0,0,0,0,0,0,0,0};
                        for (i = 0; i < HCLEN; i++) {

                            code_length_length[border[i]] = new treenode(readnbit(buf, ref ptr, 3));
                            bt_count[code_length_length[border[i]].len ]++;

                        }
                        for (; i < 19; i++) {
                            code_length_length[border[i]] =  new treenode(0);
                            bt_count[code_length_length[border[i]].len ]++;
                        }
                       code_length_length_tree = new searchtree(code_length_length,bt_count);
                        // block 1 ends

                        code_length = new treenode[HLIT + HDIST];// storing the huffman code length for the literals and code length

                        searchtree literal_length_tree;
                        searchtree distance_tree;
                        for (i = 0; i <(HLIT + HDIST);) {

                            uint bt = code_length_length_tree.decode(buf, ref ptr);
                            if (bt < 16) {
                                code_length[i] = new treenode(bt);i++;
                            }
                            else if (bt == 16) {
                                ushort cnt = (ushort)(readnbit(buf, ref ptr, 2) + 3);
                                for (; cnt > 0; cnt--,i++)
                                    code_length[i] = new treenode(code_length[i-1].len);
                            }
                            else if (bt == 17) {
                                ushort cnt =(ushort)(readnbit(buf, ref ptr, 3) + 3);
                                for (; cnt > 0; cnt--,i++)
                                    code_length[i] = new treenode(0);
                            }
                            else if (bt == 18) {
                                ushort cnt = (ushort)(readnbit(buf, ref ptr, 7) + 11);
                                for (; cnt > 0; cnt--,i++)
                                    code_length[i] =new treenode(0);
                            }
                        }
                        //call function and make two huffman treenode
                        //then use these trees to form original huffman codes and hence decompress
                        //  DebugStub.Print("length literal treenode");
                        literal_length_tree = new searchtree(code_length,0,HLIT);
                        //  DebugStub.Print("distance treenode");
                        distance_tree = new searchtree(code_length,HLIT,(uint)HLIT + HDIST);
                        // both trees made

                        //we don't need code_length array now
                        code_length = null;
                        // make dynamic treenode now

                    {   // block 2



                        val = literal_length_tree.decode(buf, ref ptr);

//                        DebugStub.Break();
                        while (val != 256) {
                            // loop till end character found
                            if (val < 256) // literal
                            {
                                bw.Write((byte)val);
                               // DebugStub.Print("{0:x},{1:x} ", __arglist(val,br.Read()));
                                circ_buf.writeindexeddata((byte)val);
                                chkcount++;
                            }
                            else // length - distance pair
                            {

                                length = read_length(buf, ref ptr,val);
                                val = distance_tree.decode(buf, ref ptr);
                                uint distance = read_dist(buf, ref ptr,val);
                                for (i = 0; i < length; i++) // copy length character from the buffer
                                {
                                    byte readbyte = circ_buf.getindexeddata(distance);
                                    bw.Write(readbyte);
                                   // DebugStub.Print("{0:x},{1:x} ",__arglist(val,br.Read());
                                    circ_buf.writeindexeddata(readbyte);
                                    chkcount++;

                                }
                            }
                           // DebugStub.Print("The value of chkcount : {0}",__arglist(chkcount));
                            val = literal_length_tree.decode(buf, ref ptr);
                        }  // while ends
                        // transfer buffer to blk.buf
                        blk.buf=ms.GetBuffer();
//                        for (uint ij = 0;ij<chkcount;ij++)
//                             DebugStub.Print("{0:x} ",__arglist(blk.buf[ij]));
                        blk.count = (int)chkcount;

                        //                  Debug.Assert((chkcount==blk.buf.Length),"count does not match "+chkcount +" " +blk.buf.Length );
                    } // block 2 ends


                    } // main block ends
                        break; // case ends

                    default:throw new Exception("Invalid Block Type");
                }  // switch ends
                //DebugStub.Break();
                BlkList.Add(blk);
            } while (!blk.last); // do while ends
           // DebugStub.Break();
          //  DebugStub.Print("Exitting decompression block");
//            if (buf.Length!=(uint)((ptr+39)/8))  // 7 to round off to next byte and 32 for the ADLER 32 chksum!
//            {
//                //DebugStub.Print("buf length {0} \t ptr {1}",__arglist(buf.Length, ptr));
//                DebugStub.Print("buf length {0} \t ptr {1}",__arglist(buf.Length, ptr));
//                 DebugStub.Break();
//                //    throw new Exception("unprocessed bits at the end of the buffer");
//            }
        } // constructor ends

        public MemoryStream getdecompressedtext()
        {
            MemoryStream decompressedText = new MemoryStream();
            foreach (Block blk in BlkList) {
                decompressedText.Write(blk.buf,0,blk.count);
                DebugStub.Print("Checkpoint 1");
            }
            DebugStub.Print("Checkpoint 2");
            return decompressedText;

        }
    } // class ends

    public class zlib
    {

        public static MemoryStream UnCompress(byte[] buf)
        {
            // extract information from the buf: for zlib header format
            ulong ptr = 0;
            // CINFO
            Compressed.readnbit(buf, ref ptr, 4);// TODO: correct the order; CINFO is not the first one
            // CM
            Compressed.readnbit(buf, ref ptr, 4);
            // FLEVEL
            Compressed.readnbit(buf, ref ptr, 2);
            // FDICT
            Compressed.readbit(buf, ref ptr);
            // FCHECK
            Compressed.readnbit(buf, ref ptr, 5);
            Compressed obj = new Compressed(buf, ref ptr);

            // ADLER32
            Compressed.readnbit(buf, ref ptr, 32);
            return obj.getdecompressedtext();
            //if (ADLER32!=getADLER32(buf))throw new Exception("Buffer Corrupted");
        }
        public static uint getADLER32(byte[] buf)
        {
            return 0;
        }

    }

    class Decompress
    {
        public static void decompress(MemoryStream compressedText,out byte[] dstbuf)
        {
            MemoryStream deCompressedText = new MemoryStream();
            compressedText.Seek( 0, SeekOrigin.Begin);
            deCompressedText = zlib.UnCompress( compressedText.GetBuffer() );
            DebugStub.Print("Checkpoint 3");
            deCompressedText.Seek( 0, SeekOrigin.Begin );
            dstbuf=deCompressedText.GetBuffer();
            compressedText = null;
            DebugStub.Print("Checkpoint 2");
        }
    }
