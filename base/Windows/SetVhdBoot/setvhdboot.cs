// ----------------------------------------------------------------------------
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
// ----------------------------------------------------------------------------

namespace BootsectorUtils
{
    using System;
    using System.IO;
    
    /// <summary>
    /// VpcFixedDiskInstaller
    ///     Console utility to install a bootsector onto a VirtualPC FIXED hard disk partition
    /// </summary>
    class VpcFixedDiskInstaller
    {
        [STAThread]
        static void Main(string[] args)
        {
            try {
                if (args.Length != 3)
                    throw new Exception("Error:  The correct argument format is <VHD Name> <Boot Sector File> <partition>");
                VpcFixedDiskInstaller i = new VpcFixedDiskInstaller();
                i.Install(args[0], args[1], Convert.ToInt32(args[2]));
            }
            catch (Exception e) {
                Console.WriteLine(e.Message);
            }
        }

        public void Install(string VHDName, string BSName, int whichPartition)
        {
            FileStream  HDFile, BSFile, BKFile;
            int         size = 512;
            int         skipsize;
            byte []     buffer = new Byte[size];
            byte []     oldBootSector = new Byte[size];
            byte []     newBootSector = new Byte[size];
            int         bytesread;
            int         MBRIndex = 446;
            int         LBA;
            string      backupFilename = "backup" + System.DateTime.Now.Ticks.ToString() + ".bootsector";


            Console.WriteLine("Setting bootsector of disk {0} in HD {1} to contents of file {2} and backing up old bootsector to {3}", 
                whichPartition, VHDName, BSName, backupFilename);

            if (whichPartition > 3 || whichPartition < 0) {
                throw new Exception("Error:  You must choose a partition between 0 and 3.");
            }

            HDFile = File.Open(VHDName, FileMode.Open, FileAccess.ReadWrite);
            
            // read the MBR from the VPC HDD file
            bytesread=HDFile.Read(buffer, 0, size);

            // branch based on partition type
            MBRIndex += ((16*whichPartition)+4);
            if ((buffer[MBRIndex] != 0x0c) && (buffer[MBRIndex] != 0x0e)) {
                throw new Exception("The partition you selected is not FAT32 type 0c or 0e.");
            }

            LBA = (int) buffer[MBRIndex+7];
            LBA = LBA*8 + buffer[MBRIndex+6];
            LBA = LBA*8 + buffer[MBRIndex+5];
            LBA = LBA*8 + buffer[MBRIndex+4];            
            
            // now that we know the location of the boot sector, let's grab it...
            HDFile.Seek((LBA)*size, SeekOrigin.Begin);
            HDFile.Read(oldBootSector, 0, size);

            // read the new BootSector
            BSFile = File.Open(BSName, FileMode.Open, FileAccess.Read);
            bytesread = BSFile.Read(newBootSector,0,size);
            if (bytesread != size) {
                throw new Exception("Error:  The boot sector is not big enough.");
            }
            if (newBootSector[510] != 0x55 || newBootSector[511] != 0xAA) {
                throw new Exception("Error:  The boot sector file has an invalid signature.");
            }
            BSFile.Close();

            skipsize = newBootSector[1]+2;

            // save the old boot sector:
            BKFile = File.OpenWrite(backupFilename);
            BKFile.Write(oldBootSector, 0, size);
            BKFile.Close();

            // generate the new boot sector by copying the BPB and FAT parameters...
            for (int i = 3; i < skipsize; i++) {
                newBootSector[i] = oldBootSector[i];
            }
            
            // point of no return:
            // write the new boot sector:
            HDFile.Seek((LBA)*size, SeekOrigin.Begin);
            HDFile.Write(newBootSector, 0, size);
            HDFile.Close();
        }
    }
}
