
//

//

//

//

//

//
//--

#include "bl.h"



#define BL_BOOT_STACK_SIZE  0x10000

PVOID BlBootStackLimit;
PVOID BlBootStackBase;

VOID
BlApEntry(
    VOID
    )


//

//

//
//--

{
    BlSingularityApEntry();

    BlRtlHalt();
}

VOID
BlInitialize(
    VOID
    )


//

//

//
//--

{
    PBEB Beb;

    Beb = BlGetBeb();

    //
    
    //

    BlRtlPrintf("Booting from ");

    switch (Beb->BootType) {

        case BL_CD_BOOT: {

            BlRtlPrintf("CD in drive 0x%02x.\n\n", Beb->BootDriveNumber);

            BlCdInitialize((UINT8) Beb->BootDriveNumber);

            break;
        }

        case BL_FAT16_BOOT: {

            BlRtlPrintf("FAT16 on drive 0x%02x.\n\n", Beb->BootDriveNumber);

            BlFatInitialize((UINT8) Beb->BootDriveNumber, MBR_FAT16LBA);

            break;
        }

        case BL_FAT32_BOOT: {

            BlRtlPrintf("FAT32 on drive 0x%02x.\n\n", Beb->BootDriveNumber);

            BlFatInitialize((UINT8) Beb->BootDriveNumber, MBR_FAT32LBA);

            break;
        }

        case BL_PXE_BOOT: {

            BlRtlPrintf("network.\n");

            BlPxeInitialize();

            break;
        }

        case BL_FLASH_BOOT: {

            BlRtlPrintf("Flash.\n");

            BlFlashInitialize((PVOID)Beb->FlashImage, (PVOID)Beb->FlashImage);

            break;
        }

        default: {

            BlRtlPrintf("unknown source!\n");

            BlRtlHalt();
        }
    }

    //
    
    //

    if (Beb->BootType != BL_FLASH_BOOT) {

        BlPnpInitialize();

    }

    //
    
    //

    BlMpsInitialize();

    //
    
    //

    if (Beb->BootType != BL_FLASH_BOOT) {

        BlAcpiInitialize();

    }
    else {

        BlAcpiNumberOfProcessors = 1;

    }

    //
    
    //

    Beb->ApEntry = (UINT32) (ULONG_PTR) BlApEntry;

    //
    
    //

    if (BlCommandLine == NULL) {

        BlCommandLine = L"";
    }

    BlSingularityInitialize(BlAcpiNumberOfProcessors,
                            &Beb->ApEntry16,
                            &Beb->ApStartupLock);
}

#if defined(BOOT_X86)

#define PLATFORM_STRING                 "x86"

#elif defined(BOOT_X64)

#define PLATFORM_STRING                 "x64"

#endif

BL_TIME BlStartTime;

VOID
BlEntry(
    VOID
    )


//

//

//
//--

{
    PBEB Beb;

    Beb = BlGetBeb();

    //
    
    //
    BlTrapEnable();

    //
    
    //

    BlVideoInitialize();

    //
    
    //

    BlRtlPrintf("Singularity %s Boot Loader [%s %s]\n"
                "\n",
                PLATFORM_STRING,
                __DATE__,
                __TIME__);

    //
    
    //

    if (Beb->BootType != BL_FLASH_BOOT) {

        BlRtlGetCurrentTime(&BlStartTime);

    }

    //
    
    //

    BlMmInitializeSystem();

    //
    
    //

    if (Beb->BootType != BL_FLASH_BOOT) {

        BlPciInitialize();

    }

    //
    
    //

    BlRtlPrintf("Looking for debugger.\n");


    //
    
    //

    BlRtlPrintf("Boot Time: %02u/%02u/%02u %02u:%02u:%02u\n",
                BlStartTime.Month,
                BlStartTime.Day,
                BlStartTime.Year,
                BlStartTime.Hour,
                BlStartTime.Minute,
                BlStartTime.Second);

    //
    
    //

#if VESA_ENABLED

    BlVesaInitialize();

#endif

    //
    
    //

    BlBootStackLimit = (PVOID) (ULONG_PTR) BlMmAllocatePhysicalRegion(BL_BOOT_STACK_SIZE, BL_MM_PHYSICAL_REGION_BOOT_STACK);
    BlBootStackBase = (PVOID) ((ULONG_PTR) BlBootStackLimit + BL_BOOT_STACK_SIZE);

    BlMmSwitchStack(BlBootStackBase, BlInitialize);
}
