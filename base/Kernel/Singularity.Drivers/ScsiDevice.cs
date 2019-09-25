////////////////////////////////////////////////////////////////////////////////
//
//  Microsoft Research Singularity
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
//  Base Classes and interfaces for SCSI Devices
//
//
//  References used:
//  "AT Attachment 8 - ATA/ATAPI Command Set (ATA8-ACS)", Revision 0, DRAFT
//          08/17/04, ISO Working Group T13, http://www.t13.org/
//
//  "SCSI Primary Commands - 3 (SPC-3)", Revision 20a, DRAFT
//          08/17/04, ISO Working Group T10, http://www.t10.org/
//
//  "SCSI Block Commands - 2 (SBC-2)", Revision 15, DRAFT
//          07/22/04, ISO Working Group T10, http://www.t10.org/
//
//  "Multimedia Commands - 4 (MMC-4)", Revision 3a, DRAFT
//          04/21/04, ISO Working Group T10, http://www.t10.org/
//
//  "Multimedia Commands - 5 (MMC-5)", Revision 0, DRAFT
//          10/11/04, ISO Working Group T10, http://www.t10.org/

using Microsoft.Singularity.Io;

using System;

namespace Microsoft.Singularity.Drivers.SCSI
{
    public enum PeripheralDeviceType
    {
        // From SPC-3, page 141
        BLOCK = 0, // Direct Access Device (hard drives), SBC
        CHAR = 1, // Sequential device (tape), SSC-2
        PRINTER = 2, // Printers (are people crazy?), SSC
        PROCESSOR = 3, // Processors (e.g. nCrypt), SPC-2
        WORM = 4, // Write once, read many, SBC
        CDROM = 5, // CD/DVD Roms, MMC
        SCANNER = 6, // Scanners (Obsolete)
        OPTICAL = 7, // Optical media, like Fujitsu MagnetoOptical. SBC
        CHANGER = 8, // Media Changers, like Jukeboxes. SMC
        COMM = 9, // Communications devices, like SCSI Ethernet.. (Obsolete)
        RAID = 12, // Storage Controllers, SCC-2
        ENCLOSURE = 13, // Enclosure Services, SES
        SIMPLE = 14, // Reduced block command devices, RBC
        OPTCARD = 15, // Optical Card Readers. OCRW
        OBJECT = 17, // Object Based Storage Device, OSD
        AUTOMAT = 18, // Automation/Drive Interface, ADC
        UNKNOWN = 31, // Unknown
    };
    public class SPC3 {
        public static string strDeviceType(PeripheralDeviceType devtype) {
            switch (devtype) {
                case PeripheralDeviceType.BLOCK:
                    return "Block Device";
                case PeripheralDeviceType.CDROM:
                    return "CD/DVD-ROM";
                default:
                    return "Unknown SCSI Device.";
            }
        }
    }
};



