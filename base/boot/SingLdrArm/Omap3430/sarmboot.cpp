//////////////////////////////////////////////////////////////////////////////
//
//  SArmBoot.cpp - Singularity ARM Boot Loader
//
//  Copyright Microsoft Corporation.
//
typedef int INT;
typedef char INT8, *PINT8;
typedef short INT16, *PINT16;
typedef long INT32, *PINT32;
typedef __int64 INT64, *PINT64;
typedef long LARGEST;
typedef char CHAR, *PCHAR;
typedef unsigned int UINT;
typedef unsigned char UINT8, *PUINT8;
typedef unsigned short UINT16, *PUINT16;
typedef unsigned long UINT32, *PUINT32;
typedef unsigned __int64 UINT64, *PUINT64;
typedef unsigned long ULARGEST;
typedef unsigned short WCHAR;
typedef unsigned char UCHAR;
typedef int BOOL;
typedef void *PVOID;
typedef UINT32 ULONG_PTR;
typedef UINT32 UINTPTR;

#define NULL    0
#define arrayof(a)      (sizeof(a)/sizeof(a[0]))
#define offsetof(s,m)   (size_t)&(((s *)0)->m)

//#define DEBUG 1

/////////////////////////////////////////// Core types used by runtime system.
//

extern "C" ULONG_PTR _security_cookie = 0;

typedef __wchar_t           bartok_char;

typedef signed char         int8;
typedef signed short        int16;
typedef signed int          int32;
typedef __int64             int64;

typedef unsigned int        uint;
typedef unsigned char       uint8;
typedef unsigned short      uint16;
typedef unsigned int        uint32;
typedef unsigned __int64    uint64;

typedef float               float32;
typedef double              float64;

typedef int                 intptr;
typedef unsigned int        uintptr;

struct uintPtr
{
    uintptr value;
};

struct intPtr
{
    intptr value;
};

typedef struct uintPtr *UIntPtr;
typedef struct intPtr *IntPtr;

//
// This saves the MiniDumpBase first time through since it gets
// updated by the kernel.
//
static uintptr DumpAddr32 = 0;

//////////////////////////////////////////////////////////////////////////////
//

/////////////////////////////////////////////////////////////// Static Assert.
//
// Compile-time (not run-time) assertion. Code will not compile if
// expr is false. Note: there is no non-debug version of this; we
// want this for all builds. The compiler optimizes the code away.
//
template <bool x> struct STATIC_ASSERT_FAILURE;
template <> struct STATIC_ASSERT_FAILURE<true> { };
template <int x> struct static_assert_test { };

#define STATIC_CAT_INNER(x,y) x##y
#define STATIC_CAT(x,y) STATIC_CAT_INNER(x,y)

#define STATIC_ASSERT(condition) \
   typedef static_assert_test< \
      sizeof(STATIC_ASSERT_FAILURE<(bool)(condition)>)> \
         STATIC_CAT(__static_assert_typedef_, __COUNTER__)

//////////////////////////////////////////////////////////////////////////////
//
#define OFFSETOF(s,m)   ((uintptr)&(((s *)0)->m))

//////////////////////////////////////////////////////////////////////////////
//
#pragma warning(disable: 4103)
#include "halclass.h"

//////////////////////////////////////////////////////////////////////////////

#define OMAP_CORE_CM_BASE              (0x48004A00)

#define CM_CLKSEL_CORE                 0x40
#define CM_CLKSEL_CORE_GPT1            0x01
#define CM_CLKSEL_CORE_GPT1_SYS32K     0x00

#define CM_CORE_EN_MMC1                (1 << 24)
#define CM_CORE_EN_MMC2                (1 << 25)
#define CM_CORE_EN_I2C1                (1 << 15)
#define CM_CORE_EN_UART2               (1 << 14)
#define CM_CORE_EN_UART1               (1 << 13)
#define CM_CORE_EN_GPT10               (1 << 11)

#define CM_FCLKEN1_CORE                (0)
#define CM_ICLKEN1_CORE                (0x10)
#define CM_ICLKEN2_CORE                (0x14)
#define CM_IDLEST_CORE                 (0x20)

#define OMAP_DSS_CM_BASE               (0x48004E00)

#define CM_FCLKEN_DSS                  (0)
#define CM_ICLKEN_DSS                  (0x10)

#define CM_DSS_EN_DSS1                 (1 << 0)
#define CM_DSS_EN_DSS2                 (1 << 1)
#define CM_DSS_EN_TV                   (1 << 2)

#define OMAP_WKUP_CM_BASE              (0x48004C00)

#define CM_CLKSEL_WKUP                 0x40
#define CM_CLKSEL_WKUP_GPT1            0x01
#define CM_CLKSEL_WKUP_GPT1_SYS32K     0x00

#define CM_WKUP_EN_GPT1                0x01
#define CM_WKUP_EN_GPIO1               (1 << 3)
#define CM_FCLKEN_WKUP                 (0)
#define CM_ICLKEN_WKUP                 (0x10)
#define CM_IDLEST_WKUP                 (0x20)

#define OMAP_PER_CM_BASE               (0x48005000)

#define CM_CLKSEL_PER                  0x40
#define CM_CLKSEL_PER_GPT2             0x01
#define CM_CLKSEL_PER_GPT2_SYS32K      0x00

#define CM_PER_EN_GPT2                 0x08
#define CM_FCLKEN_PER                  (0)
#define CM_ICLKEN_PER                  (0x10)
#define CM_IDLEST_PER                  (0x20)

//
// Registers to configure external pins for I2C, SD/MMC1, and SD/MMC2
//

#define OMAP_SCM_BASE                   (0x48002000)

#define OMAP_PADCONF_MASK               (0xffff)
#define OMAP_PADCONF_SHIFT              0x10

#define OMAP_PADCONF_MUXMODE_MASK       (0xfff8)
#define OMAP_PADCONF_MUXMODE_0          (0x0000)
#define OMAP_PADCONF_MUXMODE_1          (0x0001)
#define OMAP_PADCONF_MUXMODE_2          (0x0002)
#define OMAP_PADCONF_MUXMODE_3          (0x0003)
#define OMAP_PADCONF_MUXMODE_4          (0x0004)
#define OMAP_PADCONF_MUXMODE_5          (0x0005)
#define OMAP_PADCONF_MUXMODE_SAFE       (0x0007)
#define OMAP_PADCONF_PULLUDENABLE       (0x0008)
#define OMAP_PADCONF_PULLTYPESELECT     (0x0010)
#define OMAP_PADCONF_INPUTENABLE        (0x0100)
#define OMAP_PADCONF_OFFENABLE          (0x0200)
#define OMAP_PADCONF_OFFOUTENABLE       (0x0400)
#define OMAP_PADCONF_OFFOUTVALUE        (0x0800)
#define OMAP_PADCONF_OFFPULLUDENABLE    (0x1000)
#define OMAP_PADCONF_OFFPULLTYPESELECT  (0x2000)
#define OMAP_PADCONF_WAKEUPENABLE       (0x4000)
#define OMAP_PADCONF_WAKEUPEVENT        (0x8000)

#define OMAP_PADCONF_HSUSB0_DAT7        (0x1B8)
#define OMAP_PADCONF_I2C1_SDA           (0x1BC)
#define OMAP_PADCONF_SYS_NIRQ           (0x1E0)

#define OMAP_PADCONF_DSS_PCLK           (0x0D4)
#define OMAP_PADCONF_DSS_DAT18          (0x0FC)
#define OMAP_PADCONF_ETK_D10            (0xA40)
#define OMAP_PADCONF_ETK_D14            (0xA48)


#define OMAP_GPIO1_BASE                 (0x48310000)
#define OMAP_GPIO_OE                    (0x34)
#define OMAP_GPIO_SETDATAOUT            (0x94)
#define OMAP_GPIO_CLEARDATAOUT          (0x90)
#define OMAP_GPIO_PIN_24                (1 << 24)
#define OMAP_GPIO_PIN_28                (1 << 28)

//////////////////////////////////////////////////////////////////////////////

inline uint32 ReadReg32(volatile void * addr)
{
    return ((volatile uint32 *)addr)[0];
}

inline void WriteReg32(volatile void * addr, uint32 value)
{
    ((volatile uint32 *)addr)[0] = value;
}

inline void WriteReg16(volatile void * addr, uint16 value)
{
    ((volatile uint16 *)addr)[0] = value;
}

inline uint16 ReadReg16(volatile void * addr)
{
    return ((volatile uint16 *)addr)[0];
}

inline void WriteReg8(volatile void * addr, uint8 value)
{
    ((volatile uint8 *)addr)[0] = value;
}

inline uint8 ReadReg8(volatile void * addr)
{
    return ((volatile uint8 *)addr)[0];
}

//////////////////////////////////////////////////////////////////////////////
//

typedef unsigned int uint;
typedef unsigned int UINT;
typedef signed long LARGEST;
typedef unsigned long ULARGEST;

#include "strformat.cpp"
#include "printf.cpp"
#include "debuguart.cpp"
#include "debug.cpp"
#include "expandpe.cpp"

//////////////////////////////////////////////////////////////////////////////
//
void Halt(void);

#define ASSERT(b)   if (!(b)) { AssertFailed(#b);} else
void AssertFailed(const char *string)
{
    printf("Assert Failed [%s]\n", string);
    Halt();
}

////////////////////////////////////////////////////////////////////// Memory.
//
//  OMAP 3430 Memory Map:
//
#define ON_OMAP3430_RESERVE_ADDR    0x80000000
#define ON_OMAP3430_RESERVE_SIZE    0x00050000

#define ON_OMAP3430_LOADER_ADDR     0x80000000  // SArmBoot code.
#define ON_OMAP3430_LOADER_SIZE     0x0000fff0  // was 0x10000.

#define ON_OMAP3430_CPU_ARGS_ADDR   0x8000fff0  //
#define ON_OMAP3430_CPU_ARGS_SIZE   0x80000010  //

#define ON_OMAP3430_VIDEO_ADDR      0x80010000  // LCD Video.
#define ON_OMAP3430_VIDEO_SIZE      0x00025800

#define ON_OMAP3430_ALLOC_ADDR      0x80035800  // Boot "alloc()" heap.
#define ON_OMAP3430_ALLOC_SIZE      0x0000A800

#define ON_OMAP3430_LOGBUF_ADDR     0x80040000  // Logging record buffer.
#define ON_OMAP3430_LOGBUF_SIZE     0x00008000

#define ON_OMAP3430_LOGTXT_ADDR     0x80048000  // Logging text buffer.
#define ON_OMAP3430_LOGTXT_SIZE     0x00008000

#define ON_OMAP3430_STACK_ADDR      0x80050000  // Kernel stack.
#define ON_OMAP3430_STACK_SIZE      0x00010000

#define ON_OMAP3430_KERNEL_ADDR     0x80100000  // Base address of kernel.
//#define ON_OMAP3430_KERNEL_SIZE   0xFFFFFFFF  // Determined at runtime.

#define ON_OMAP3430_MEMORY_ADDR     0x80000000  // Base general memory.
#define ON_OMAP3430_MEMORY_SIZE     0x08000000

#define ON_OMAP3430_IFLASH_ADDR     0x84000000  // Memory to scan for flash image.
#define ON_OMAP3430_IFLASH_SIZE     0x04000000

//
// These should be in a general memory layout file
// rather than buried deeply in code
//
static uintptr heapTop = ON_OMAP3430_ALLOC_ADDR;
static uintptr heapMax = ON_OMAP3430_ALLOC_ADDR + ON_OMAP3430_ALLOC_SIZE;

extern "C" void * memset(void *dest, uint8 c, uint count);
extern "C" void * memmove(void *dest, const void *src, uint count);

void * alloc(uint cbSize, uint cbPad)
{
    cbPad = (cbPad != 0) ? ((cbPad + 0xf) & ~0xf) : 0x10;  // 16-byte pad minimum.
    uintptr newTop = (heapTop + (cbPad - 1)) & ~(cbPad - 1);
    void *pvData = (void *)newTop;

    cbSize = (cbSize != 0) ? ((cbSize + 0xf) & ~0xf) : 0x10;   //16-byte pad minimum.
    newTop += cbSize;
    if (newTop  > heapMax) {
        // Failure, no one checks this call
        printf("alloc failure req %d\n", cbSize);
        Halt();
        return NULL;
    }
    heapTop = newTop;
    memset(pvData, 0, cbSize);
    return pvData;
}

void * alloc(uint cbSize)
{
    return alloc(cbSize, 0x10);
}

void * allocpages(uint cPages)
{
    return alloc(Class_Microsoft_Singularity_Hal_Platform_PAGE_SIZE * cPages,
                 Class_Microsoft_Singularity_Hal_Platform_PAGE_SIZE);
}

void * operator new(uint cbSize)
{
    return alloc(cbSize, 0);
}

///////////////////////////////////////////////////////////// Screen Routines.
//

#define DISPC_REVISION              0x00
#define DISPC_SYSCONFIG             0x10
#define DISPC_SYSSTATUS             0x14
#define DISPC_IRQSTATUS             0x18
#define DISPC_IRQENABLE             0x1C
#define DISPC_CONTROL               0x40
#define DISPC_CONFIG                0x44
#define DISPC_CAPABLE               0x48
#define DISPC_DEFAULT_COLOR0        0x4C
#define DISPC_DEFAULT_COLOR1        0x50
#define DISPC_TRANS_COLOR0          0x54
#define DISPC_TRANS_COLOR1          0x58
#define DISPC_LINE_STATUS           0x5C
#define DISPC_LINE_NUMBER           0x60
#define DISPC_TIMING_H              0x64
#define DISPC_TIMING_V              0x68
#define DISPC_POL_FREQ              0x6C
#define DISPC_DIVISOR               0x70
#define DISPC_SIZE_DIG              0x78
#define DISPC_SIZE_LCD              0x7C
#define DISPC_GFX_BA0               0x80
#define DISPC_GFX_BA1               0x84
#define DISPC_GFX_POSITION          0x88
#define DISPC_GFX_SIZE              0x8C
#define DISPC_GFX_ATTRIBUTES        0xA0
#define DISPC_GFX_FIFO_THRESHOLD    0xA4
#define DISPC_GFX_FIFO_SIZE_STATUS  0xA8
#define DISPC_GFX_ROW_INC           0xAC
#define DISPC_GFX_PIXEL_INC         0xB0
#define DISPC_GFX_WINDOW_SKIP       0xB4
#define DISPC_GFX_TABLE_BA          0xB8
#define DISPC_VID1_BA0              0xBC
#define DISPC_VID1_BA1              0xC0
#define DISPC_VID1_POSITION         0xC4
#define DISPC_VID1_SIZE             0xC8
#define DISPC_VID1_ATTRIBUTES       0xCC
#define DISPC_VID1_FIFO_THRESHOLD   0xD0
#define DISPC_VID1_FIFO_SIZE_STATUS 0xD4
#define DISPC_VID1_ROW_INC          0xD8
#define DISPC_VID1_PIXEL_INC        0xDC
#define DISPC_VID1_FIR              0xE0
#define DISPC_VID1_PICTURE_SIZE     0xE4
#define DISPC_VID1_ACCU0            0xE8
#define DISPC_VID1_ACCU1            0xEC
#define DISPC_VID1_CONV_COEF0       0x130
#define DISPC_VID1_CONV_COEF1       0x134
#define DISPC_VID1_CONV_COEF2       0x138
#define DISPC_VID1_CONV_COEF3       0x13C
#define DISPC_VID1_CONV_COEF4       0x140
#define DISPC_VID2_BA0              0x14C
#define DISPC_VID2_BA1              0x150
#define DISPC_VID2_POSITION         0x154
#define DISPC_VID2_SIZE             0x158
#define DISPC_VID2_ATTRIBUTES       0x15C
#define DISPC_VID2_FIFO_THRESHOLD   0x160
#define DISPC_VID2_FIFO_SIZE_STATUS 0x164
#define DISPC_VID2_ROW_INC          0x168
#define DISPC_VID2_PIXEL_INC        0x16C
#define DISPC_VID2_FIR              0x170
#define DISPC_VID2_PICTURE_SIZE     0x174
#define DISPC_VID2_ACCU0            0x178
#define DISPC_VID2_ACCU1            0x17C
#define DISPC_VID2_CONV_COEF0       0x1C0
#define DISPC_VID2_CONV_COEF1       0x1C4
#define DISPC_VID2_CONV_COEF2       0x1C8
#define DISPC_VID2_CONV_COEF3       0x1CC
#define DISPC_VID2_CONV_COEF4       0x1D0
#define DISPC_DATA_CYCLE1           0x1D4
#define DISPC_DATA_CYCLE2           0x1D8
#define DISPC_DATA_CYCLE3           0x1DC
#define DISPC_CPR_COEF_R            0x220
#define DISPC_CPR_COEF_G            0x224
#define DISPC_CPR_COEF_B            0x228
#define DISPC_GFX_PRELOAD           0x22C
#define DISPC_VID1_PRELOAD          0x230
#define DISPC_VID2_PRELOAD          0x234

#define DISPC_CONFIG_LOADMODE_FRDATLEF  (2 << 1) //  XXX maybe

#define DISPC_CONTROL_DIGITALENABLE (1 << 1)
#define DISPC_CONTROL_GOLCD         (1 << 5)
#define DISPC_CONTROL_GPOUT0        (1 << 15)
#define DISPC_CONTROL_GPOUT1        (1 << 16)
#define DISPC_CONTROL_LCDENABLE     (1 << 0)
#define DISPC_CONTROL_RFBIMODE      (1 << 11)
#define DISPC_CONTROL_STNTFT        (1 << 3)
#define DISPC_CONTROL_TFTDATALINES_OALSB16B (1 << 8)

#define DISPC_DIVISOR_LCD_SHIFT     16
#define DISPC_DIVISOR_PCD_SHIFT     0

#define DISPC_GFX_ATTRIBUTES_ENABLE 1
#define DISPC_GFX_ATTRIBUTES_GFXFORMAT_RGB16 (6 << 1)

#define DISPC_GFX_FIFO_THRESHOLD_HIGH_SHIFT 16
#define DISPC_GFX_FIFO_THRESHOLD_LOW_SHIFT 0

#define DISPC_SYSCONFIG_MIDLEMODE_NSTANDBY (1 << 12)
#define DISPC_SYSCONFIG_SIDLEMODE_NIDLE    (1 << 3)
#define DISPC_SYSCONFIG_SOFTRESET          (1 << 1)

#define DISPC_SYSSTATUS_RESETDONE          (1)

#define DISPC_TIMING_H_HBP_SHIFT    20
#define DISPC_TIMING_H_HFP_SHIFT    8
#define DISPC_TIMING_H_HSW_SHIFT    0

#define DISPC_TIMING_V_VBP_SHIFT    20
#define DISPC_TIMING_V_VFP_SHIFT    8
#define DISPC_TIMING_V_VSW_SHIFT    0

#define DISPC_SIZE_LCD_QVGA_PORTRAIT (((320 - 1) << 16) | (240 - 1))
#define DISPC_SIZE_QVGA_PORTRAIT    DISPC_SIZE_LCD_QVGA_PORTRAIT

#define GPIO_LCD_BACKLIGHT          24
#define GPIO_LCD_POWER              28

//////////////////////////////////////////////////////////////////////////////
//
//
// I2C interface (used here to control power to SD/MMC cards via the 4030)
//

#define OMAP_I2C1_BASE                 (0x48070000)

#define I2C_STAT                       (0x8)
#define I2C_STAT_XDR                   (1 << 14)
#define I2C_STAT_RDR                   (1 << 13)
#define I2C_STAT_BUSY                  (1 << 12)
#define I2C_STAT_XRDY                  (1 << 4)
#define I2C_STAT_RRDY                  (1 << 3)
#define I2C_STAT_ARDY                  (1 << 2)
#define I2C_STAT_NACK                  (1 << 1)
#define I2C_STAT_AL                    (1 << 0)

#define I2C_BUF                        (0x14)
#define I2C_CNT                        (0x18)
#define I2C_DATA                       (0x1C)

#define I2C_CON                        (0x24)
#define I2C_CON_EN                     (1 << 15)
#define I2C_CON_STB                    (1 << 11)  // XXX REVIEW
#define I2C_CON_MASTER                 (1 << 10)
#define I2C_CON_DIR_MASK               (1 << 9)
#define I2C_CON_XMIT                   I2C_CON_DIR_MASK
#define I2C_CON_RECV                   (0)
#define I2C_CON_STP                    (1 << 1) // XXX REVIEW
#define I2C_CON_STT                    (1 << 0) // XXX REVIEW

#define I2C_PSC                        (0x30)
#define I2C_SCLL                       (0x34)
#define I2C_SCLH                       (0x38)
#define I2C_OA0                        (0x28)
#define I2C_SA                         (0x2C)
#define I2C_BUFSTAT                    (0x40)

#define OMAP_PM_RECEIVER               (0x4B)

void HalpClocksInitialize()
{
    uint32 Value;

    // Clock manager domain control registers
    uint8 * HalpWKUP_CM = (uint8 *)OMAP_WKUP_CM_BASE;
    uint8 * HalpCORE_CM = (uint8 *)OMAP_CORE_CM_BASE;
    uint8 * HalpDSS_CM  = (uint8 *)OMAP_DSS_CM_BASE;

    // Enable interface and function clocks for WKUP (power management)
    Value = ReadReg32(HalpWKUP_CM + CM_FCLKEN_WKUP);
    Value |= CM_WKUP_EN_GPIO1;
    WriteReg32(HalpWKUP_CM + CM_FCLKEN_WKUP, Value);

    Value = ReadReg32(HalpWKUP_CM + CM_ICLKEN_WKUP);
    Value |= CM_WKUP_EN_GPIO1;
    WriteReg32(HalpWKUP_CM + CM_ICLKEN_WKUP, Value);

    // Enable interface and function clocks for CORE (peripherals)
    Value = ReadReg32(HalpCORE_CM + CM_FCLKEN1_CORE);
    Value |= CM_CORE_EN_I2C1;
    WriteReg32(HalpCORE_CM + CM_FCLKEN1_CORE, Value);

    Value = ReadReg32(HalpCORE_CM + CM_ICLKEN1_CORE);
    Value |= CM_CORE_EN_I2C1;
    WriteReg32(HalpCORE_CM + CM_ICLKEN1_CORE,Value);

    // Enable interface and function clocks for DSS (display)
    Value = ReadReg32(HalpDSS_CM + CM_FCLKEN_DSS);
    Value |= CM_DSS_EN_DSS1 | CM_DSS_EN_DSS2 | CM_DSS_EN_TV;
    WriteReg32(HalpDSS_CM + CM_FCLKEN_DSS, Value);

    Value = ReadReg32(HalpDSS_CM + CM_ICLKEN_DSS);
    Value |= CM_DSS_EN_DSS1;
    WriteReg32(HalpDSS_CM + CM_ICLKEN_DSS, Value);
}

void HalpGpioInitialize()
{
    uint32 Value;
    uint8 * HalpSCM = (uint8 *)OMAP_SCM_BASE;

    //
    // Configure GPIO pads
    //
    // NB: mode 7 is 'safe' mode - GPIO as input with
    //     no function selected from multiplexer
    //

    // Enable i2c1_scl

    // OMAP_PADCONF_HSUSB0_DAT7[15:0]  is hsusb0_data7 (mode 0),
    // OMAP_PADCONF_HSUSB0_DAT7[31:16] is i2c1_scl (mode 0)
    Value = ReadReg32(HalpSCM + OMAP_PADCONF_HSUSB0_DAT7);
    // i2c1_scl mux mode 7 (reset) -> mode 0
    Value &= ((OMAP_PADCONF_MUXMODE_MASK << OMAP_PADCONF_SHIFT) | OMAP_PADCONF_MASK);
    WriteReg32(HalpSCM + OMAP_PADCONF_HSUSB0_DAT7,Value);

    // Enable i2c1_sda

    // OMAP_PADCONF_I2C1_SDA[15:0]  is i2c1_sda (mode 0),
    // OMAP_PADCONF_I2C1_SDA[31:16] is i2c2_scl (mode 0)
    Value = ReadReg32(HalpSCM + OMAP_PADCONF_I2C1_SDA);
    // i2c1_sda mux mode 7 (reset) -> mode 0 */
    Value &= ((OMAP_PADCONF_MASK << OMAP_PADCONF_SHIFT) | OMAP_PADCONF_MUXMODE_MASK);
    WriteReg32(HalpSCM + OMAP_PADCONF_I2C1_SDA,Value);

    // Enable sys_nirq
    // - connected to int1_n on TWL4030

    // OMAP_PADCONF_SYS_NIRQ[15:0]  is sys_nirq (mode 0),
    // OMAP_PADCONF_SYS_NIRQ[31:16] is sys_clkout2 (mode 0)
    Value = ReadReg32(HalpSCM + OMAP_PADCONF_SYS_NIRQ);
    // sys_nirq mux mode 7 (reset) -> mode 0
    Value &= ((OMAP_PADCONF_MASK << OMAP_PADCONF_SHIFT) | OMAP_PADCONF_MUXMODE_MASK);
    WriteReg32(HalpSCM + OMAP_PADCONF_I2C1_SDA,Value);

    // Enable dss_* for LCD; configure these as:
    //  PULLTYPESELECT = 0, PULLUDENABLE = 0, output
    uint8 * LcdGpioConfigRegister = (uint8 *)OMAP_SCM_BASE + OMAP_PADCONF_DSS_PCLK;
    uint8* const LcdGpioConfigRegisterEnd = (uint8 *)OMAP_SCM_BASE + OMAP_PADCONF_DSS_DAT18;

    // OMAP_PADCONF_DSS_PCLK[15:0]   is dss_pclk (mode 0),
    // OMAP_PADCONF_DSS_PCLK[31:16]  is dss_hsync (mode 0),
    // OMAP_PADCONF_DSS_VSYNC[15:0]  is dss_vsync (mode 0),
    // OMAP_PADCONF_DSS_VSYNC[31:16] is dss_acbias (mode 0),
    // OMAP_PADCONF_DSS_DATn[15:0]   is dss_data(n) (mode 0),
    // OMAP_PADCONF_DSS_DATn[31:16]  is dss_data(n+1) (mode 0)
    for (; LcdGpioConfigRegister <= LcdGpioConfigRegisterEnd; LcdGpioConfigRegister += 4) {
        WriteReg32(LcdGpioConfigRegister, (OMAP_PADCONF_MUXMODE_0 << OMAP_PADCONF_SHIFT) | OMAP_PADCONF_MUXMODE_0);
    }

    // [arog - Do we need to configure etk_d15/11 as well as gpio_24/28?]

    // OMAP_PADCONF_ETK_D14[15:0]  is gpio_28 (mode 4),
    // OMAP_PADCONF_ETK_D14[31:16] is etk_d15 (mode 0) */
    WriteReg32(HalpSCM + OMAP_PADCONF_ETK_D14, (OMAP_PADCONF_MUXMODE_0 << OMAP_PADCONF_SHIFT) | OMAP_PADCONF_MUXMODE_4);

    // OMAP_PADCONF_ETK_D10[15:0]  is gpio_24 (mode 4),
    // OMAP_PADCONF_ETK_D10[31:16] is etk_d11 (mode 0)
    WriteReg32(HalpSCM + OMAP_PADCONF_ETK_D10, (OMAP_PADCONF_MUXMODE_0 << OMAP_PADCONF_SHIFT) | OMAP_PADCONF_MUXMODE_4);
}

void HalpI2CMasterInitialize()
{
    uint16 ShortValue;
    uint8 * HalpI2C1 = (uint8 *)OMAP_I2C1_BASE;

    // Setup I2C1 controller
    // _ARM_WORKAROUND_ i2c code is erroring out
    if ((ReadReg16(HalpI2C1 + I2C_CON) & I2C_CON_EN) != 0) {
        ShortValue = ReadReg16(HalpI2C1 + I2C_CON);
        ShortValue &= I2C_CON_EN;
        WriteReg16(HalpI2C1 + I2C_CON, ShortValue);
        ReadReg16(HalpI2C1 + I2C_CON);
    }

    ASSERT((ReadReg16(HalpI2C1 + I2C_CON) & I2C_CON_EN) == 0);
    // We should handle the case where it was already enabled.

    // Configure internal sampling frequency for 12Mhz.
    WriteReg8(HalpI2C1 + I2C_PSC, 7);

    // Configure for 100 kb/s
    WriteReg8(HalpI2C1 + I2C_SCLL, 54);
    WriteReg8(HalpI2C1 + I2C_SCLH, 56);

    // Set own address address register
    WriteReg16(HalpI2C1 + I2C_OA0, 0x21);

    // Take I2C controller out of reset
    ShortValue = ReadReg16(HalpI2C1 + I2C_CON);
    ShortValue |= I2C_CON_EN;
    WriteReg16(HalpI2C1 + I2C_CON,ShortValue);
}

void HalpI2CMasterSetup(
    bool Xmit,
    uint8 SlaveAddress,
    uint16 Length,
    bool GenerateStart,
    bool GenerateStop
    )
{
    uint16 ShortValue;
    uint8 * HalpI2C1 = (uint8 *)OMAP_I2C1_BASE;

    WriteReg16(HalpI2C1 + I2C_CON,I2C_CON_EN);

    // Set slave address
    WriteReg16(HalpI2C1 + I2C_SA,SlaveAddress);

    // Set transfer length
    WriteReg16(HalpI2C1 + I2C_CNT,Length);

    // Clear status
    WriteReg16(HalpI2C1 + I2C_STAT,
               I2C_STAT_ARDY | I2C_STAT_NACK | I2C_STAT_AL);

    // wait for free bus?
    //    while ReadReg16(HalpI2C1 + I2C_STAT)) & I2C_STAT_BUSY);

    ShortValue = I2C_CON_EN | I2C_CON_MASTER;
    ShortValue |= Xmit ? I2C_CON_XMIT : I2C_CON_RECV;
    ShortValue |= GenerateStart ? I2C_CON_STT : 0;
    ShortValue |= GenerateStop ? I2C_CON_STP : 0;

    WriteReg16(HalpI2C1 + I2C_CON,ShortValue);
}

bool HalpI2CMasterTransfer(bool Xmit, uint16 Length, uint8 * Data)
{
    uint16 Stat;
    uint16 Room;
    uint8 * HalpI2C1 = (uint8 *)OMAP_I2C1_BASE;

    for (;;) {

        Stat = ReadReg16(HalpI2C1 + I2C_STAT);

        if (Stat & (I2C_STAT_NACK|I2C_STAT_AL)) {
            ASSERT(Stat == 0);
            return false;
        }

        if (Stat & (I2C_STAT_ARDY)) {
            return true;
        }

        if (Xmit) {
            if (Stat & I2C_STAT_XDR) {
                Room = ReadReg16(HalpI2C1 + I2C_BUFSTAT) & 0x3F;
                while (Room--) {
                    WriteReg8(HalpI2C1 + I2C_DATA, *Data);
                    Data++;
                    Length--;
                }
            }

            if (Stat & I2C_STAT_XRDY) {
                Room = ReadReg16(HalpI2C1 + I2C_BUF) & 0x3F;
                Room += 1;

                while (Room--) {
                    WriteReg8(HalpI2C1 + I2C_DATA, *Data);
                    Data++;
                    Length--;
                }
            }
        }
        else {
            if (Stat & I2C_STAT_RDR) {
                Room = (ReadReg16(HalpI2C1 + I2C_BUFSTAT) >> 8) & 0x3F;

                while (Room--) {
                    *Data = ReadReg8(HalpI2C1 + I2C_DATA);
                    Data++;
                    Length--;
                }
            }

            if (Stat & I2C_STAT_RRDY) {
                Room = (ReadReg16(HalpI2C1 + I2C_BUF) >> 8) & 0x3F;
                Room += 1;

                while (Room--) {
                    *Data = ReadReg8(HalpI2C1 + I2C_DATA);
                    Data++;
                    Length--;
                }
            }
        }

        WriteReg16(HalpI2C1 + I2C_STAT,Stat);
    }

    return true;
}

bool
HalpI2CMasterCommon(
    bool Xmit,
    uint8 SlaveAddress,
    uint16 Length,
    uint8 * Data,
    bool GenerateStart,
    bool GenerateStop
    )
{
    int retry = 10;

    while (retry--) {

        HalpI2CMasterSetup(Xmit, OMAP_PM_RECEIVER, Length, GenerateStart, GenerateStop);

        if (HalpI2CMasterTransfer(Xmit, Length, Data)) {
            return true;
        }
    }
    return false;
}

bool
HalpI2CMasterReceive(
    uint8 SlaveAddress,
    uint16 Length,
    uint8 * Data,
    bool GenerateStart,
    bool GenerateStop
    )
{
    return HalpI2CMasterCommon(false, OMAP_PM_RECEIVER, Length, Data,
                               GenerateStart, GenerateStop);
}

bool
HalpI2CMasterSend(
    uint8 SlaveAddress,
    uint16 Length,
    uint8 * Data,
    bool GenerateStart,
    bool GenerateStop
    )
{
    return HalpI2CMasterCommon(true, OMAP_PM_RECEIVER, Length, Data,
                               GenerateStart, GenerateStop);
}

//////////////////////////////////////////////////////////////////////////////
//
void InitializeDisplayPowerDomains()
{
    uint32 Value;
    bool Good;
    uint32 Count;
    uint8 Data[2];

    //
    // Bootstrap VAUX3
    //

    Data[0] = 0x7A;
    Data[1] = 1 << 5;
    Good = HalpI2CMasterSend(OMAP_PM_RECEIVER, 2, Data, true, true);
    ASSERT(Good);

    Data[0] = 0x7B;
    Data[1] = 4;
    Good = HalpI2CMasterSend(OMAP_PM_RECEIVER, 2, Data, true, true);
    ASSERT(Good);

    Data[0] = 0x7d;
    Data[1] = 0x3;
    Good = HalpI2CMasterSend(OMAP_PM_RECEIVER, 2, Data, true, true);
    ASSERT(Good);

    Data[0] = 0x7d;
    Good = HalpI2CMasterSend(OMAP_PM_RECEIVER, 1, Data, true, false);
    ASSERT(Good);
    Good = HalpI2CMasterReceive(OMAP_PM_RECEIVER, 1, Data, true, true);
    ASSERT(Good);
    ASSERT(Data[0] == 3);

    Count = 0xFFFF;
    while (Count--);

    uint8 * HalpGPIO1 = (uint8 *)OMAP_GPIO1_BASE;

    Value = ReadReg32(HalpGPIO1 + OMAP_GPIO_OE);
    Value &= ~(OMAP_GPIO_PIN_24 | OMAP_GPIO_PIN_28);
    WriteReg32(HalpGPIO1 + OMAP_GPIO_OE, Value);

    WriteReg32(HalpGPIO1 + OMAP_GPIO_SETDATAOUT, OMAP_GPIO_PIN_28);

    Count = 0xFFFF;
    while (Count--);

    WriteReg32(HalpGPIO1 + OMAP_GPIO_SETDATAOUT, OMAP_GPIO_PIN_24);
}

//////////////////////////////////////////////////////////////////////////////

uint8 Font8[] =
    {
        0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,
        0x7e,0x81,0xa5,0x81,0xbd,0x99,0x81,0x7e,
        0x7e,0xff,0xdb,0xff,0xc3,0xe7,0xff,0x7e,
        0x6c,0xfe,0xfe,0xfe,0x7c,0x38,0x10,0x00,
        0x10,0x38,0x7c,0xfe,0x7c,0x38,0x10,0x00,
        0x38,0x7c,0x38,0xfe,0xfe,0x7c,0x38,0x7c,
        0x10,0x10,0x38,0x7c,0xfe,0x7c,0x38,0x7c,
        0x00,0x00,0x18,0x3c,0x3c,0x18,0x00,0x00,
        0xff,0xff,0xe7,0xc3,0xc3,0xe7,0xff,0xff,
        0x00,0x3c,0x66,0x42,0x42,0x66,0x3c,0x00,
        0xff,0xc3,0x99,0xbd,0xbd,0x99,0xc3,0xff,
        0x0f,0x07,0x0f,0x7d,0xcc,0xcc,0xcc,0x78,
        0x3c,0x66,0x66,0x66,0x3c,0x18,0x7e,0x18,
        0x3f,0x33,0x3f,0x30,0x30,0x70,0xf0,0xe0,
        0x7f,0x63,0x7f,0x63,0x63,0x67,0xe6,0xc0,
        0x99,0x5a,0x3c,0xe7,0xe7,0x3c,0x5a,0x99,
        0x80,0xe0,0xf8,0xfe,0xf8,0xe0,0x80,0x00,
        0x02,0x0e,0x3e,0xfe,0x3e,0x0e,0x02,0x00,
        0x18,0x3c,0x7e,0x18,0x18,0x7e,0x3c,0x18,
        0x66,0x66,0x66,0x66,0x66,0x00,0x66,0x00,
        0x7f,0xdb,0xdb,0x7b,0x1b,0x1b,0x1b,0x00,
        0x3e,0x63,0x38,0x6c,0x6c,0x38,0xcc,0x78,
        0x00,0x00,0x00,0x00,0x7e,0x7e,0x7e,0x00,
        0x18,0x3c,0x7e,0x18,0x7e,0x3c,0x18,0xff,
        0x18,0x3c,0x7e,0x18,0x18,0x18,0x18,0x00,
        0x18,0x18,0x18,0x18,0x7e,0x3c,0x18,0x00,
        0x00,0x18,0x0c,0xfe,0x0c,0x18,0x00,0x00,
        0x00,0x30,0x60,0xfe,0x60,0x30,0x00,0x00,
        0x00,0x00,0xc0,0xc0,0xc0,0xfe,0x00,0x00,
        0x00,0x24,0x66,0xff,0x66,0x24,0x00,0x00,
        0x00,0x18,0x3c,0x7e,0xff,0xff,0x00,0x00,
        0x00,0xff,0xff,0x7e,0x3c,0x18,0x00,0x00,
        0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,
        0x30,0x78,0x78,0x30,0x30,0x00,0x30,0x00,
        0x6c,0x6c,0x6c,0x00,0x00,0x00,0x00,0x00,
        0x6c,0x6c,0xfe,0x6c,0xfe,0x6c,0x6c,0x00,
        0x30,0x7c,0xc0,0x78,0x0c,0xf8,0x30,0x00,
        0x00,0xc6,0xcc,0x18,0x30,0x66,0xc6,0x00,
        0x38,0x6c,0x38,0x76,0xdc,0xcc,0x76,0x00,
        0x60,0x60,0xc0,0x00,0x00,0x00,0x00,0x00,
        0x18,0x30,0x60,0x60,0x60,0x30,0x18,0x00,
        0x60,0x30,0x18,0x18,0x18,0x30,0x60,0x00,
        0x00,0x66,0x3c,0xff,0x3c,0x66,0x00,0x00,
        0x00,0x30,0x30,0xfc,0x30,0x30,0x00,0x00,
        0x00,0x00,0x00,0x00,0x00,0x30,0x30,0x60,
        0x00,0x00,0x00,0xfc,0x00,0x00,0x00,0x00,
        0x00,0x00,0x00,0x00,0x00,0x30,0x30,0x00,
        0x06,0x0c,0x18,0x30,0x60,0xc0,0x80,0x00,
        0x7c,0xc6,0xce,0xde,0xf6,0xe6,0x7c,0x00,
        0x30,0x70,0x30,0x30,0x30,0x30,0xfc,0x00,
        0x78,0xcc,0x0c,0x38,0x60,0xcc,0xfc,0x00,
        0x78,0xcc,0x0c,0x38,0x0c,0xcc,0x78,0x00,
        0x1c,0x3c,0x6c,0xcc,0xfe,0x0c,0x1e,0x00,
        0xfc,0xc0,0xf8,0x0c,0x0c,0xcc,0x78,0x00,
        0x38,0x60,0xc0,0xf8,0xcc,0xcc,0x78,0x00,
        0xfc,0xcc,0x0c,0x18,0x30,0x30,0x30,0x00,
        0x78,0xcc,0xcc,0x78,0xcc,0xcc,0x78,0x00,
        0x78,0xcc,0xcc,0x7c,0x0c,0x18,0x70,0x00,
        0x00,0x30,0x30,0x00,0x00,0x30,0x30,0x00,
        0x00,0x30,0x30,0x00,0x00,0x30,0x30,0x60,
        0x18,0x30,0x60,0xc0,0x60,0x30,0x18,0x00,
        0x00,0x00,0xfc,0x00,0x00,0xfc,0x00,0x00,
        0x60,0x30,0x18,0x0c,0x18,0x30,0x60,0x00,
        0x78,0xcc,0x0c,0x18,0x30,0x00,0x30,0x00,
        0x7c,0xc6,0xde,0xde,0xde,0xc0,0x78,0x00,
        0x30,0x78,0xcc,0xcc,0xfc,0xcc,0xcc,0x00,
        0xfc,0x66,0x66,0x7c,0x66,0x66,0xfc,0x00,
        0x3c,0x66,0xc0,0xc0,0xc0,0x66,0x3c,0x00,
        0xf8,0x6c,0x66,0x66,0x66,0x6c,0xf8,0x00,
        0xfe,0x62,0x68,0x78,0x68,0x62,0xfe,0x00,
        0xfe,0x62,0x68,0x78,0x68,0x60,0xf0,0x00,
        0x3c,0x66,0xc0,0xc0,0xce,0x66,0x3e,0x00,
        0xcc,0xcc,0xcc,0xfc,0xcc,0xcc,0xcc,0x00,
        0x78,0x30,0x30,0x30,0x30,0x30,0x78,0x00,
        0x1e,0x0c,0x0c,0x0c,0xcc,0xcc,0x78,0x00,
        0xe6,0x66,0x6c,0x78,0x6c,0x66,0xe6,0x00,
        0xf0,0x60,0x60,0x60,0x62,0x66,0xfe,0x00,
        0xc6,0xee,0xfe,0xfe,0xd6,0xc6,0xc6,0x00,
        0xc6,0xe6,0xf6,0xde,0xce,0xc6,0xc6,0x00,
        0x38,0x6c,0xc6,0xc6,0xc6,0x6c,0x38,0x00,
        0xfc,0x66,0x66,0x7c,0x60,0x60,0xf0,0x00,
        0x78,0xcc,0xcc,0xcc,0xdc,0x78,0x1c,0x00,
        0xfc,0x66,0x66,0x7c,0x6c,0x66,0xe6,0x00,
        0x78,0xcc,0xe0,0x70,0x1c,0xcc,0x78,0x00,
        0xfc,0xb4,0x30,0x30,0x30,0x30,0x78,0x00,
        0xcc,0xcc,0xcc,0xcc,0xcc,0xcc,0xfc,0x00,
        0xcc,0xcc,0xcc,0xcc,0xcc,0x78,0x30,0x00,
        0xc6,0xc6,0xc6,0xd6,0xfe,0xee,0xc6,0x00,
        0xc6,0xc6,0x6c,0x38,0x38,0x6c,0xc6,0x00,
        0xcc,0xcc,0xcc,0x78,0x30,0x30,0x78,0x00,
        0xfe,0xc6,0x8c,0x18,0x32,0x66,0xfe,0x00,
        0x78,0x60,0x60,0x60,0x60,0x60,0x78,0x00,
        0xc0,0x60,0x30,0x18,0x0c,0x06,0x02,0x00,
        0x78,0x18,0x18,0x18,0x18,0x18,0x78,0x00,
        0x10,0x38,0x6c,0xc6,0x00,0x00,0x00,0x00,
        0x00,0x00,0x00,0x00,0x00,0x00,0x00,0xff,
        0x30,0x30,0x18,0x00,0x00,0x00,0x00,0x00,
        0x00,0x00,0x78,0x0c,0x7c,0xcc,0x76,0x00,
        0xe0,0x60,0x60,0x7c,0x66,0x66,0xdc,0x00,
        0x00,0x00,0x78,0xcc,0xc0,0xcc,0x78,0x00,
        0x1c,0x0c,0x0c,0x7c,0xcc,0xcc,0x76,0x00,
        0x00,0x00,0x78,0xcc,0xfc,0xc0,0x78,0x00,
        0x38,0x6c,0x60,0xf0,0x60,0x60,0xf0,0x00,
        0x00,0x00,0x76,0xcc,0xcc,0x7c,0x0c,0xf8,
        0xe0,0x60,0x6c,0x76,0x66,0x66,0xe6,0x00,
        0x30,0x00,0x70,0x30,0x30,0x30,0x78,0x00,
        0x0c,0x00,0x0c,0x0c,0x0c,0xcc,0xcc,0x78,
        0xe0,0x60,0x66,0x6c,0x78,0x6c,0xe6,0x00,
        0x70,0x30,0x30,0x30,0x30,0x30,0x78,0x00,
        0x00,0x00,0xcc,0xfe,0xfe,0xd6,0xc6,0x00,
        0x00,0x00,0xf8,0xcc,0xcc,0xcc,0xcc,0x00,
        0x00,0x00,0x78,0xcc,0xcc,0xcc,0x78,0x00,
        0x00,0x00,0xdc,0x66,0x66,0x7c,0x60,0xf0,
        0x00,0x00,0x76,0xcc,0xcc,0x7c,0x0c,0x1e,
        0x00,0x00,0xdc,0x76,0x66,0x60,0xf0,0x00,
        0x00,0x00,0x7c,0xc0,0x78,0x0c,0xf8,0x00,
        0x10,0x30,0x7c,0x30,0x30,0x34,0x18,0x00,
        0x00,0x00,0xcc,0xcc,0xcc,0xcc,0x76,0x00,
        0x00,0x00,0xcc,0xcc,0xcc,0x78,0x30,0x00,
        0x00,0x00,0xc6,0xd6,0xfe,0xfe,0x6c,0x00,
        0x00,0x00,0xc6,0x6c,0x38,0x6c,0xc6,0x00,
        0x00,0x00,0xcc,0xcc,0xcc,0x7c,0x0c,0xf8,
        0x00,0x00,0xfc,0x98,0x30,0x64,0xfc,0x00,
        0x1c,0x30,0x30,0xe0,0x30,0x30,0x1c,0x00,
        0x18,0x18,0x18,0x00,0x18,0x18,0x18,0x00,
        0xe0,0x30,0x30,0x1c,0x30,0x30,0xe0,0x00,
        0x76,0xdc,0x00,0x00,0x00,0x00,0x00,0x00,
        0x00,0x10,0x38,0x6c,0xc6,0xc6,0xfe,0x00,
        0x78,0xcc,0xc0,0xcc,0x78,0x18,0x0c,0x78,
        0x00,0xcc,0x00,0xcc,0xcc,0xcc,0x7e,0x00,
        0x1c,0x00,0x78,0xcc,0xfc,0xc0,0x78,0x00,
        0x7e,0xc3,0x3c,0x06,0x3e,0x66,0x3f,0x00,
        0xcc,0x00,0x78,0x0c,0x7c,0xcc,0x7e,0x00,
        0xe0,0x00,0x78,0x0c,0x7c,0xcc,0x7e,0x00,
        0x30,0x30,0x78,0x0c,0x7c,0xcc,0x7e,0x00,
        0x00,0x00,0x78,0xc0,0xc0,0x78,0x0c,0x38,
        0x7e,0xc3,0x3c,0x66,0x7e,0x60,0x3c,0x00,
        0xcc,0x00,0x78,0xcc,0xfc,0xc0,0x78,0x00,
        0xe0,0x00,0x78,0xcc,0xfc,0xc0,0x78,0x00,
        0xcc,0x00,0x70,0x30,0x30,0x30,0x78,0x00,
        0x7c,0xc6,0x38,0x18,0x18,0x18,0x3c,0x00,
        0xe0,0x00,0x70,0x30,0x30,0x30,0x78,0x00,
        0xc6,0x38,0x6c,0xc6,0xfe,0xc6,0xc6,0x00,
        0x30,0x30,0x00,0x78,0xcc,0xfc,0xcc,0x00,
        0x1c,0x00,0xfc,0x60,0x78,0x60,0xfc,0x00,
        0x00,0x00,0x7f,0x0c,0x7f,0xcc,0x7f,0x00,
        0x3e,0x6c,0xcc,0xfe,0xcc,0xcc,0xce,0x00,
        0x78,0xcc,0x00,0x78,0xcc,0xcc,0x78,0x00,
        0x00,0xcc,0x00,0x78,0xcc,0xcc,0x78,0x00,
        0x00,0xe0,0x00,0x78,0xcc,0xcc,0x78,0x00,
        0x78,0xcc,0x00,0xcc,0xcc,0xcc,0x7e,0x00,
        0x00,0xe0,0x00,0xcc,0xcc,0xcc,0x7e,0x00,
        0x00,0xcc,0x00,0xcc,0xcc,0x7c,0x0c,0xf8,
        0xc3,0x18,0x3c,0x66,0x66,0x3c,0x18,0x00,
        0xcc,0x00,0xcc,0xcc,0xcc,0xcc,0x78,0x00,
        0x18,0x18,0x7e,0xc0,0xc0,0x7e,0x18,0x18,
        0x38,0x6c,0x64,0xf0,0x60,0xe6,0xfc,0x00,
        0xcc,0xcc,0x78,0xfc,0x30,0xfc,0x30,0x30,
        0xf8,0xcc,0xcc,0xfa,0xc6,0xcf,0xc6,0xc7,
        0x0e,0x1b,0x18,0x3c,0x18,0x18,0xd8,0x70,
        0x1c,0x00,0x78,0x0c,0x7c,0xcc,0x7e,0x00,
        0x38,0x00,0x70,0x30,0x30,0x30,0x78,0x00,
        0x00,0x1c,0x00,0x78,0xcc,0xcc,0x78,0x00,
        0x00,0x1c,0x00,0xcc,0xcc,0xcc,0x7e,0x00,
        0x00,0xf8,0x00,0xf8,0xcc,0xcc,0xcc,0x00,
        0xfc,0x00,0xcc,0xec,0xfc,0xdc,0xcc,0x00,
        0x3c,0x6c,0x6c,0x3e,0x00,0x7e,0x00,0x00,
        0x38,0x6c,0x6c,0x38,0x00,0x7c,0x00,0x00,
        0x30,0x00,0x30,0x60,0xc0,0xcc,0x78,0x00,
        0x00,0x00,0x00,0xfc,0xc0,0xc0,0x00,0x00,
        0x00,0x00,0x00,0xfc,0x0c,0x0c,0x00,0x00,
        0xc3,0xc6,0xcc,0xde,0x33,0x66,0xcc,0x0f,
        0xc3,0xc6,0xcc,0xdb,0x37,0x6f,0xcf,0x03,
        0x18,0x18,0x00,0x18,0x18,0x18,0x18,0x00,
        0x00,0x33,0x66,0xcc,0x66,0x33,0x00,0x00,
        0x00,0xcc,0x66,0x33,0x66,0xcc,0x00,0x00,
        0x22,0x88,0x22,0x88,0x22,0x88,0x22,0x88,
        0x55,0xaa,0x55,0xaa,0x55,0xaa,0x55,0xaa,
        0xdb,0x77,0xdb,0xee,0xdb,0x77,0xdb,0xee,
        0x18,0x18,0x18,0x18,0x18,0x18,0x18,0x18,
        0x18,0x18,0x18,0x18,0xf8,0x18,0x18,0x18,
        0x18,0x18,0xf8,0x18,0xf8,0x18,0x18,0x18,
        0x36,0x36,0x36,0x36,0xf6,0x36,0x36,0x36,
        0x00,0x00,0x00,0x00,0xfe,0x36,0x36,0x36,
        0x00,0x00,0xf8,0x18,0xf8,0x18,0x18,0x18,
        0x36,0x36,0xf6,0x06,0xf6,0x36,0x36,0x36,
        0x36,0x36,0x36,0x36,0x36,0x36,0x36,0x36,
        0x00,0x00,0xfe,0x06,0xf6,0x36,0x36,0x36,
        0x36,0x36,0xf6,0x06,0xfe,0x00,0x00,0x00,
        0x36,0x36,0x36,0x36,0xfe,0x00,0x00,0x00,
        0x18,0x18,0xf8,0x18,0xf8,0x00,0x00,0x00,
        0x00,0x00,0x00,0x00,0xf8,0x18,0x18,0x18,
        0x18,0x18,0x18,0x18,0x1f,0x00,0x00,0x00,
        0x18,0x18,0x18,0x18,0xff,0x00,0x00,0x00,
        0x00,0x00,0x00,0x00,0xff,0x18,0x18,0x18,
        0x18,0x18,0x18,0x18,0x1f,0x18,0x18,0x18,
        0x00,0x00,0x00,0x00,0xff,0x00,0x00,0x00,
        0x18,0x18,0x18,0x18,0xff,0x18,0x18,0x18,
        0x18,0x18,0x1f,0x18,0x1f,0x18,0x18,0x18,
        0x36,0x36,0x36,0x36,0x37,0x36,0x36,0x36,
        0x36,0x36,0x37,0x30,0x3f,0x00,0x00,0x00,
        0x00,0x00,0x3f,0x30,0x37,0x36,0x36,0x36,
        0x36,0x36,0xf7,0x00,0xff,0x00,0x00,0x00,
        0x00,0x00,0xff,0x00,0xf7,0x36,0x36,0x36,
        0x36,0x36,0x37,0x30,0x37,0x36,0x36,0x36,
        0x00,0x00,0xff,0x00,0xff,0x00,0x00,0x00,
        0x36,0x36,0xf7,0x00,0xf7,0x36,0x36,0x36,
        0x18,0x18,0xff,0x00,0xff,0x00,0x00,0x00,
        0x36,0x36,0x36,0x36,0xff,0x00,0x00,0x00,
        0x00,0x00,0xff,0x00,0xff,0x18,0x18,0x18,
        0x00,0x00,0x00,0x00,0xff,0x36,0x36,0x36,
        0x36,0x36,0x36,0x36,0x3f,0x00,0x00,0x00,
        0x18,0x18,0x1f,0x18,0x1f,0x00,0x00,0x00,
        0x00,0x00,0x1f,0x18,0x1f,0x18,0x18,0x18,
        0x00,0x00,0x00,0x00,0x3f,0x36,0x36,0x36,
        0x36,0x36,0x36,0x36,0xff,0x36,0x36,0x36,
        0x18,0x18,0xff,0x18,0xff,0x18,0x18,0x18,
        0x18,0x18,0x18,0x18,0xf8,0x00,0x00,0x00,
        0x00,0x00,0x00,0x00,0x1f,0x18,0x18,0x18,
        0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,
        0x00,0x00,0x00,0x00,0xff,0xff,0xff,0xff,
        0xf0,0xf0,0xf0,0xf0,0xf0,0xf0,0xf0,0xf0,
        0x0f,0x0f,0x0f,0x0f,0x0f,0x0f,0x0f,0x0f,
        0xff,0xff,0xff,0xff,0x00,0x00,0x00,0x00,
        0x00,0x00,0x76,0xdc,0xc8,0xdc,0x76,0x00,
        0x00,0x78,0xcc,0xf8,0xcc,0xf8,0xc0,0xc0,
        0x00,0xfc,0xcc,0xc0,0xc0,0xc0,0xc0,0x00,
        0x00,0xfe,0x6c,0x6c,0x6c,0x6c,0x6c,0x00,
        0xfc,0xcc,0x60,0x30,0x60,0xcc,0xfc,0x00,
        0x00,0x00,0x7e,0xd8,0xd8,0xd8,0x70,0x00,
        0x00,0x66,0x66,0x66,0x66,0x7c,0x60,0xc0,
        0x00,0x76,0xdc,0x18,0x18,0x18,0x18,0x00,
        0xfc,0x30,0x78,0xcc,0xcc,0x78,0x30,0xfc,
        0x38,0x6c,0xc6,0xfe,0xc6,0x6c,0x38,0x00,
        0x38,0x6c,0xc6,0xc6,0x6c,0x6c,0xee,0x00,
        0x1c,0x30,0x18,0x7c,0xcc,0xcc,0x78,0x00,
        0x00,0x00,0x7e,0xdb,0xdb,0x7e,0x00,0x00,
        0x06,0x0c,0x7e,0xdb,0xdb,0x7e,0x60,0xc0,
        0x38,0x60,0xc0,0xf8,0xc0,0x60,0x38,0x00,
        0x78,0xcc,0xcc,0xcc,0xcc,0xcc,0xcc,0x00,
        0x00,0xfc,0x00,0xfc,0x00,0xfc,0x00,0x00,
        0x30,0x30,0xfc,0x30,0x30,0x00,0xfc,0x00,
        0x60,0x30,0x18,0x30,0x60,0x00,0xfc,0x00,
        0x18,0x30,0x60,0x30,0x18,0x00,0xfc,0x00,
        0x0e,0x1b,0x1b,0x18,0x18,0x18,0x18,0x18,
        0x18,0x18,0x18,0x18,0x18,0xd8,0xd8,0x70,
        0x30,0x30,0x00,0xfc,0x00,0x30,0x30,0x00,
        0x00,0x76,0xdc,0x00,0x76,0xdc,0x00,0x00,
        0x38,0x6c,0x6c,0x38,0x00,0x00,0x00,0x00,
        0x00,0x00,0x00,0x18,0x18,0x00,0x00,0x00,
        0x00,0x00,0x00,0x00,0x18,0x00,0x00,0x00,
        0x0f,0x0c,0x0c,0x0c,0xec,0x6c,0x3c,0x1c,
        0x78,0x6c,0x6c,0x6c,0x6c,0x00,0x00,0x00,
        0x70,0x18,0x30,0x60,0x78,0x00,0x00,0x00,
        0x00,0x00,0x3c,0x3c,0x3c,0x3c,0x00,0x00,
        0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00,
    };

static uint32 videoCursor = 0;
static uint16 * videoBuffer = 0;

void InitializeDisplay(uint16 * VideoBuffer)
{
    InitializeDisplayPowerDomains();

    videoBuffer = VideoBuffer;

    uint8 * DispCRegBase = (uint8 *)0x48050400;

    //
    // XXX code derived from TI diagnostic, tainted.
    //

    // xxx dss_clock_init

    //
    // disable dss
    //

    uint32 Value = ReadReg32(DispCRegBase + DISPC_CONTROL);
    Value &= ~(DISPC_CONTROL_DIGITALENABLE | DISPC_CONTROL_LCDENABLE);
    WriteReg32(DispCRegBase + DISPC_CONTROL, Value);

    //
    // Reset display controller
    //

    WriteReg32(DispCRegBase + DISPC_SYSCONFIG, DISPC_SYSCONFIG_SOFTRESET);

    while((ReadReg32(DispCRegBase + DISPC_SYSSTATUS) & DISPC_SYSSTATUS_RESETDONE) == 0);
    Value = ReadReg32(DispCRegBase + DISPC_SYSCONFIG);
    Value &= ~DISPC_SYSCONFIG_SOFTRESET;
    WriteReg32(DispCRegBase + DISPC_SYSCONFIG, Value);


    //
    // _ARM_WORKAROUND_ cheat and setup lcd power and backlight
    // earlier in HAL.  Right way to do this is with query interface
    // of the stack to get a control interface.
    //
    // XXX do triton thing here to enable lcd power, and thena  gpio that i don't understand
    // xxx gpio thing to enable backlight

    // configure dss

    WriteReg32(DispCRegBase + DISPC_SYSCONFIG,
               DISPC_SYSCONFIG_MIDLEMODE_NSTANDBY |
               DISPC_SYSCONFIG_SIDLEMODE_NIDLE);

    // disable interrupts
    WriteReg32(DispCRegBase + DISPC_IRQENABLE, 0);

    // 2:1 - Frame Data only loaded every frame (10)

    WriteReg32(DispCRegBase + DISPC_CONFIG,
               DISPC_CONFIG_LOADMODE_FRDATLEF);

    // Default Color is white
    WriteReg32(DispCRegBase + DISPC_DEFAULT_COLOR0,
               0xFFFFFF);

    // Default Transparency Color is black */
    WriteReg32(DispCRegBase + DISPC_TRANS_COLOR0, 0);

    // timing logic for HSYNC signal

    uint32 bp = (3 - 1);
    uint32 fp = (4 - 1);
    uint32 sw = (2 - 1);

    Value = (bp << DISPC_TIMING_H_HBP_SHIFT) | (fp << DISPC_TIMING_H_HFP_SHIFT) | (sw << DISPC_TIMING_H_HSW_SHIFT);
    WriteReg32(DispCRegBase + DISPC_TIMING_H, Value);

    // timing logic for VSYNC signal

    bp = 6;
    fp = 9;
    sw = 1;

    Value = (bp << DISPC_TIMING_V_VBP_SHIFT) | (fp << DISPC_TIMING_V_VFP_SHIFT) | (sw << DISPC_TIMING_V_VSW_SHIFT);
    WriteReg32(DispCRegBase + DISPC_TIMING_V, Value);

    // signal configuration
    WriteReg32(DispCRegBase + DISPC_POL_FREQ, 0);

    // configures the divisor
    Value = (1 << DISPC_DIVISOR_LCD_SHIFT) | (17 << DISPC_DIVISOR_PCD_SHIFT);
    WriteReg32(DispCRegBase + DISPC_DIVISOR, Value);

    // configure panel size
    WriteReg32(DispCRegBase + DISPC_SIZE_LCD,
               DISPC_SIZE_LCD_QVGA_PORTRAIT);

    // set lcd interface datalines
    // defaults to 16

    // Configure Graphics Window
    WriteReg32(DispCRegBase + DISPC_GFX_BA0, (uint32)VideoBuffer);
    WriteReg32(DispCRegBase + DISPC_GFX_BA1, (uint32)VideoBuffer);

    // set window position
    WriteReg32(DispCRegBase + DISPC_GFX_POSITION, 0);

    // set window size
    WriteReg32(DispCRegBase + DISPC_GFX_SIZE, DISPC_SIZE_QVGA_PORTRAIT);

    Value = ReadReg32(DispCRegBase + DISPC_GFX_ATTRIBUTES);
    Value |= DISPC_GFX_ATTRIBUTES_GFXFORMAT_RGB16;
    WriteReg32(DispCRegBase + DISPC_GFX_ATTRIBUTES, Value);

    Value= (252 << DISPC_GFX_FIFO_THRESHOLD_HIGH_SHIFT) | (192 << DISPC_GFX_FIFO_THRESHOLD_LOW_SHIFT);

    WriteReg32(DispCRegBase + DISPC_GFX_FIFO_THRESHOLD, Value);

    WriteReg32(DispCRegBase + DISPC_GFX_ROW_INC, 1);

    WriteReg32(DispCRegBase + DISPC_GFX_PIXEL_INC, 1);

    Value = ReadReg32(DispCRegBase + DISPC_GFX_ATTRIBUTES);
    Value |= DISPC_GFX_ATTRIBUTES_ENABLE;
    WriteReg32(DispCRegBase + DISPC_GFX_ATTRIBUTES, Value);

    // LCD output enabled, active display,16-bit output.
    Value = DISPC_CONTROL_GPOUT1 | DISPC_CONTROL_GPOUT0
        | DISPC_CONTROL_TFTDATALINES_OALSB16B | DISPC_CONTROL_STNTFT |
        DISPC_CONTROL_LCDENABLE;
    Value &= ~DISPC_CONTROL_RFBIMODE; // RFBI mode disabled.
    WriteReg32(DispCRegBase + DISPC_CONTROL, Value);

    Value = ReadReg32(DispCRegBase + DISPC_CONTROL);
    Value |= DISPC_CONTROL_GOLCD; // LCD GO command.
    WriteReg32(DispCRegBase + DISPC_CONTROL, Value);

    memset(VideoBuffer, 0xff, 240 * 320 * 2);
}

void Draw(uint8 c)
{
    if (videoBuffer == NULL) {
        return;
    }

    if (c == '\f') {
        videoCursor = 0;
        memset(videoBuffer, 0, 240 * 320 * 2);
        return;
    }
    else if (c == '\n') {
        videoCursor += 30 - (videoCursor % 30);
      check_scroll:
        while (videoCursor >= 30 * 40) {
            memmove(videoBuffer, videoBuffer + 240 * 8, 240 * 312 * 2);
            memset(videoBuffer + 312 * 240, 0, 240 * 16);    // 2 bytes/pixel * 8 pixels
            videoCursor -= 30;
        }
        return;
    }

    uint cy = (videoCursor / 30) * 8;
    uint cx = (videoCursor % 30) * 8;
    uint16 * buffer = videoBuffer + 240 * cy + cx;

    if (c == '\r') {
        uint toclear = 30 - (videoCursor % 30);

        for (uint y = 0; y < 8; y++) {
            memset(buffer, 0, toclear * 16);    // 2 bytes/pixel * 8 pixels
            buffer += 240;
        }
        videoCursor -= videoCursor % 30;
        return;
    }

    // Find the glyph.
    uint8 *pixels = Font8 + c * 8;

    // Draw the pixels.
    for (uint y = 0; y < 8; y++) {
        uint8 line = *pixels++;
        for (int x = 7; x >= 0; x--) {
            buffer[x] = (line & 1) ? 0xffff : 0x0000;
            line >>= 1;
        }
        buffer += 240;
    }
    videoCursor++;
    goto check_scroll;
}

void Draw(const char * str)
{
    for (int i = 0; i < 2048 && str[i] != '\0'; i++) {
        Draw((uint8)str[i]);
    }
}

//////////////////////////////////////////////////////////////////////////////

void DebugBreak();

void Halt()
{
    printf("Halt.");
    DebugBreak();
}

void Cls()
{
    BdPrintString("-------------------------------------------------------------------------------\n", 80);
    Draw('\f');
}

void __cdecl PutChar(char cOut)
{
    Draw(cOut);

    static CHAR szBuffer[256];
    static INT nBuffer = 0;

    szBuffer[nBuffer++] = cOut;
    if (cOut == '\n' || nBuffer >= sizeof(szBuffer) - 1) {
        BdPrintString(szBuffer, nBuffer);
        nBuffer = 0;
    }
}

void Probe(UINT8 * pbData, UINT cbData)
{
    UINT8 b;

    for (UINT i = 0; i < cbData; i++) {
        b = pbData[i];
        pbData[i] = b;
    }
}

void Dump(UINT8 * pbData, UINT cbData)
{
    for (UINT n = 0; n < cbData; n += 16) {
        printf("  %08x:", pbData + n);
        UINT o = n;
        for (; o < n + 16; o++) {
            if (o >= cbData) {
                printf("  ");
            }
            else {
                printf("%02x", pbData[o]);
            }
            if (o % 4 == 3) {
                printf(" ");
            }
        }
        printf(" ");
        for (o = n; o < n + 16; o++) {
            if (o >= cbData) {
                printf("  ");
            }
            else {
                if (pbData[o] >= ' ' && pbData[o] < 127) {
                    printf("%c", pbData[o]);
                }
                else {
                    printf(".");
                }
            }
        }
        printf("\n");
    }
}

void Dump(UINT8 * pbData, UINT8 * pbLimit, UINT cbMax)
{
    UINT cbData = (uint) (pbLimit - pbData);
    if (cbData > cbMax) {
        cbData = cbMax;
    }
    Dump(pbData, cbData);
}

static void CopyDown(UINT8 *pbDst, UINT8 *pbSrc, UINT32 cbSrc)
{
    //!!! pbDst <= pbSrc
    if (pbDst > pbSrc) {
        printf("CopyDown(dst=%p > src=%p)\n", pbDst, pbSrc);
        Halt();
    }

    INT32 nSrc = (cbSrc + 3) / 4;
    volatile UINT32 *pDst = (UINT32*)pbDst;
    volatile UINT32 *pSrc = (UINT32*)pbSrc;

    while (nSrc-- > 0) {
        *pDst = *pSrc;
        if (*pDst != *pSrc) {
            printf("CopyDown error at %p/%p : %08x != %08x\n",
                   pDst, pSrc, *pDst, *pSrc);
            Halt();
        }
        pDst++;
        pSrc++;
    }
}

static void Zero(uint8 * pbData, uint32 cbData)
{
    INT32 nDst = (cbData + 3) / 4;
    volatile UINT32 *pDst = (UINT32*)pbData;

    while (nDst-- > 0) {
        *pDst++ = 0;
    }
}

const char * SmapTypeToString(int type)
{
    switch (type) {
      case 1: return "RAM     ";
      case 2: return "Reserved";
      case 3: return "ACPI RAM";
      case 4: return "ACPI NVS";
      default: return "Other   ";
    }
}

bool check(UINT8 *pbCache, UINT8 value, const char *pszDesc)
{
    for (int i = 0; i < 16; i++) {
        if (pbCache[i] == value) {
            pbCache[i] = 0;
            printf("      %s\n", pszDesc);
            return 1;
        }
    }
    return 0;
}

static bool CheckSmapForRam(const Class_Microsoft_Singularity_Hal_Platform *bi, UINT64 base, UINT64 size)
{
    Struct_Microsoft_Singularity_SMAPINFO *sm = (Struct_Microsoft_Singularity_SMAPINFO *) bi->Smap32;
    for (int32 i = 0; i < bi->SmapCount; i++) {
        if (sm[i].type == 1 &&
            sm[i].addr <= base &&
            sm[i].addr + sm[i].size >= base + size) {

            return true;
        }
    }
    return false;
}

static void CheckSmap(const Class_Microsoft_Singularity_Hal_Platform *bi)
{
    /////////////////////////////////////////////////////// System Memory Map.
    //
    printf(" BaseAddr LimtAddr Type      \n");
    printf(" ======== ======== ========== [%8x]\n", bi->Smap32);

    Struct_Microsoft_Singularity_SMAPINFO *sm = (Struct_Microsoft_Singularity_SMAPINFO *) bi->Smap32;
    for (int32 i = 0; i < bi->SmapCount; i++) {
        printf(" %8x", (UINT32)(sm[i].addr));
        printf(" %8x", (UINT32)(sm[i].addr + sm[i].size));
        printf(" %d:%s\n",
               sm[i].type,
               SmapTypeToString((int)sm[i].type));
    }
    printf("\n");
}

void SortSmap(const Class_Microsoft_Singularity_Hal_Platform *bi)
{
    Struct_Microsoft_Singularity_SMAPINFO *sm = (Struct_Microsoft_Singularity_SMAPINFO *) bi->Smap32;
    // Sort the system memory map.
  sortagain:
    for (int i = 0; i < bi->SmapCount - 1; i++) {
        if ((sm[i].addr > sm[i + 1].addr) ||
            (sm[i].addr == sm[i + 1].addr &&
             sm[i].addr > sm[i + 1].addr)) {

            Struct_Microsoft_Singularity_SMAPINFO s = sm[i];
            sm[i] = sm[i+1];
            sm[i+1] = s;

            goto sortagain;
        }
    }
}

static uintptr g_Entry = 0;
static uintptr g_Stack = 0;
static Class_Microsoft_Singularity_Hal_Platform  *g_bi = 0;
static Class_Microsoft_Singularity_Hal_Cpu *g_ci = 0;

//////////////////////////////////////////////////////////////////////////////

static bool memeq(const uint8 * p1, const uint8 * p2, uint size)
{
    for (; size > 0; size--) {
        if (*p1++ != *p2++) {
            return false;
        }
    }
    return true;
}

struct FlashHead
{
    uint8   label[18];
    uint8   headSize;
    uint8   fileSize;
    uint32  pageSize;
    uint32  majorVersion;
    uint32  minorVersion;
};

struct FlashFile
{
    uint32  pathOffset;
    uint32  dataOffset;
    uint32  size;
};

uintptr FindFlashImage(uintptr begin, uintptr limit)
{
    // Round begin and limit to nearest valid addresses.
    begin = (begin + 0xffff) & ~(uintptr)0xffff;
    limit = (limit + 0xffff) & ~(uintptr)0xffff;

    // walk through at 64KB boundaries looking for flash image.
    for (; begin < limit ; begin += 0x10000) {
        const FlashHead * head = (const FlashHead *)begin;
        if (!memeq(head->label, (uint8*)"SingularityFlash!", sizeof(head->label))) {
            continue;
        }
        if (head->headSize != sizeof(FlashHead)) {
            continue;
        }
        if (head->fileSize != sizeof(FlashFile)) {
            continue;
        }
        if (head->majorVersion != ~0u || head->minorVersion != ~0u) {
            continue;
        }
        if (head->pageSize != 0x1000) {
            continue;
        }

        // Header values all check out, now look at image content.

        const FlashFile *file = (FlashFile*)(head + 1);
        const FlashFile *fend = file + 8192;
        for (; file < fend; file++) {
            if ((file->dataOffset == 0xffffffff && file->size == 0xffffffff) ||
                (file->dataOffset == 0 && file->size == 0)) {
                continue;
            }
            else if (file->dataOffset == 0xffffffff && file->size == 0) {
                return begin;
            }
            else if ((file->dataOffset & 0xfff) != 0) {
                // file has unaligned offset.
                printf("Unaligned offset: %x\n", file);
                break;
            }
        }
    }
    return 0;
}

uintptr SizeFlashImage(uintptr begin, uint& count)
{
    uintptr limit = 0;
    count = 0;

    const FlashHead * head = (const FlashHead *)begin;
    const FlashFile *file = (FlashFile*)(head + 1);

    // Assumes that there is always at least one valid file in the flash.
    for (;; file++) {
        if ((file->dataOffset == 0xffffffff && file->size == 0xffffffff) ||
            (file->dataOffset == 0 && file->size == 0)) {
            continue;
        }
        else if (file->dataOffset == 0xffffffff && file->size == 0) {
            break;
        }

        if (limit < file->dataOffset + file->size) {
            limit = file->dataOffset + file->size;
        }
        count++;
    }

    return ((limit + 0xfff) & ~0xfff);
}

void ProcessFlashImage(uintptr begin,
                       Struct_Microsoft_Singularity_Io_FileImage *files, uint count)
{
    const FlashHead * head = (const FlashHead *)begin;
    const FlashFile *file = (FlashFile*)(head + 1);

    // Assumes that there is always at least one valid file in the flash.
    for (uint item = 0;; file++) {
        if ((file->dataOffset == 0xffffffff && file->size == 0xffffffff) ||
            (file->dataOffset == 0 && file->size == 0)) {
            continue;
        }
        else if (file->dataOffset == 0xffffffff && file->size == 0) {
            break;
        }

        if (item < count) {
            files[item].Address = begin + file->dataOffset;
            files[item].Size = file->size;
            item++;
        }
    }
}

//////////////////////////////////////////////////////////////////////////////
//

extern uintptr GetStack(void);
extern uintptr GetCode(void);
extern uint32 GetMidr(void);
extern uint32 GetPfr0(void);
extern uint32 GetPfr1(void);
extern uintptr GetVbar(void);
extern void SetVbar(uintptr);
extern void SetTpidrurw(uintptr);

uint MpStartupLock = 0;

int BootPhase1(void)
{
    HalpClocksInitialize();
    HalpGpioInitialize();
    HalpI2CMasterInitialize();

    BdInitDebugger(BdPortInit((uint32 *)OMAP_UART1_BASE, 115200));
    printf("\f\n\rSingularity ARM Boot Loader [" __DATE__ " "__TIME__ "]\n\r");

    InitializeDisplay((uint16 *)ON_OMAP3430_VIDEO_ADDR);
    Draw("\fSingularity ARM Boot Loader\n[" __DATE__ " "__TIME__ "]\n\r");

    uintptr base;
    uintptr size = SizeOfPeImage((uintptr)ON_OMAP3430_LOADER_ADDR, base);

    ASSERT(size <= ON_OMAP3430_LOADER_SIZE);

    // Find out what kind of processor we're running on.
    uint32 midr = GetMidr();
    switch ((midr & 0xff000000) >> 24) {
      case 0x41: printf("ARM Ltd "); break;
      case 0x44: printf("DEC "); break;
      case 0x4d: printf("Motorola "); break;
      case 0x51: printf("Qualcomm "); break;
      case 0x56: printf("Marvell "); break;
      case 0x69: printf("Intel "); break;
      default: printf("Implementor? ");

    }
    switch ((midr & 0xf0000) >> 16) {
      case 0x01: printf("ARMv4 "); break;
      case 0x02: printf("ARMv4T "); break;
      case 0x03: printf("ARMv5 "); break;
      case 0x04: printf("ARMv5T "); break;
      case 0x05: printf("ARMv5TE "); break;
      case 0x06: printf("ARMv5TEJ "); break;
      case 0x07: printf("ARMv6 "); break;
      case 0x0f: printf("ARMv7 "); break;
      default: printf("Variant? "); break;
    }
    printf("%x.%x\n", (midr & 0xfff0) >> 4, midr & 0xf);

    if ((midr & 0xf0000) == 0xf0000) {
        // ARMv7, Used CPUID scheme.
        printf("PFR: 0:%08x, 1:%08x\n", GetPfr0(), GetPfr1());
    }
    printf("\n");

    //
    // Get the BIOS info
    //
    g_bi = (Class_Microsoft_Singularity_Hal_Platform *)
        alloc(sizeof(Class_Microsoft_Singularity_Hal_Platform));
    g_bi->Size = sizeof(Class_Microsoft_Singularity_Hal_Platform);

    //
    // Save the debug information.
    //
    g_bi->DebugBasePort = OMAP_UART1_BASE;

    //
    // Set up Memory Map
    //
    Struct_Microsoft_Singularity_SMAPINFO *sm =
        (Struct_Microsoft_Singularity_SMAPINFO *)
        alloc(sizeof(Struct_Microsoft_Singularity_SMAPINFO) * 32);

    g_bi->Smap32 = (uintptr)sm;

    // Remember loader.
    sm[0].type = Struct_Microsoft_Singularity_SMAPINFO_AddressTypeReserved;
    sm[0].addr = ON_OMAP3430_LOADER_ADDR;
    sm[0].size = SizeOfPeImage((uintptr)ON_OMAP3430_LOADER_ADDR, base);

    // Remember other low reserved.
    sm[1].type = Struct_Microsoft_Singularity_SMAPINFO_AddressTypeReserved;
    sm[1].addr = ON_OMAP3430_RESERVE_ADDR + sm[0].size;
    sm[1].size = ON_OMAP3430_RESERVE_SIZE - (sm[1].addr - ON_OMAP3430_RESERVE_ADDR);

    // Remember RAM.
    sm[2].type = Struct_Microsoft_Singularity_SMAPINFO_AddressTypeFree;
    sm[2].addr = ON_OMAP3430_STACK_ADDR;
    sm[2].size = ON_OMAP3430_MEMORY_SIZE - (ON_OMAP3430_STACK_ADDR - ON_OMAP3430_MEMORY_ADDR);

    // Mark off I/O memory
    sm[3].type = Struct_Microsoft_Singularity_SMAPINFO_AddressTypeUnusable;
    sm[3].addr = 0;
    sm[3].size = 0x80000000;

    g_bi->SmapCount = 4;

    //
    // Register the boot memory that we use to allocated classes
    // that will be converted into managed classes once the kernel
    // initializes. This is so it can be properly reported to the
    // GC.
    //
    // Record the entire boot memory range so that the kernel does
    // not use it for working memory
    //
    g_bi->BootAllocatedMemory = 0;
    g_bi->BootAllocatedMemorySize = 0x00400000; // Leave this as a guess of memory usage

    g_bi->CpuRealCount = 1;
    g_bi->CpuMaxCount = 1;
    g_bi->BootCount = 0;

    g_bi->LogRecordBuffer   = ON_OMAP3430_LOGBUF_ADDR; // See Platform.cs
    g_bi->LogRecordSize     = ON_OMAP3430_LOGBUF_SIZE;
    g_bi->LogTextBuffer     = ON_OMAP3430_LOGTXT_ADDR;
    g_bi->LogTextSize       = ON_OMAP3430_LOGTXT_SIZE;
    g_bi->KernelDllFirstPage=
    g_bi->KernelDllBase     = ON_OMAP3430_KERNEL_ADDR;
    g_bi->PhysicalBase      = 0x00010000;

    //
    // NOTE: The singldr should edit the SMAP to not include memory
    //       allocated to the kernel, its stacks, etc, similar to busying
    //       out the dump record.
    //
    //       This would be a cleaner communication than the current
    //       combination of SMAP's, kernel base etc.
    //
    //       There has been discussion of a modified version of SMAP that
    //       is communicated to the kernel that describes how memory has
    //       been used. SMAP describes general memory information, while
    //       the kernel needs to know how memory taken from the SMAP was
    //       used. This is important for the kernel to build its GC
    //       structures that track which pages contain GC objects.
    //

    g_bi->CpuMaxCount = 1;

    g_ci = (Class_Microsoft_Singularity_Hal_Cpu *)
        alloc(sizeof(Class_Microsoft_Singularity_Hal_Cpu) * 1);
    g_bi->Cpus = (uintptr)g_ci;
    g_ci->Size = sizeof(Class_Microsoft_Singularity_Hal_Cpu);
    g_ci->Id = 0;
    g_ci->KernelStackLimit = ON_OMAP3430_STACK_ADDR; // See also Platform.cs
    g_ci->KernelStackBegin = ON_OMAP3430_STACK_ADDR + ON_OMAP3430_STACK_SIZE;

    // Default to the Serial debugger
    g_bi->DebuggerType = Class_Microsoft_Singularity_Hal_Platform_DEBUGGER_SERIAL;

    g_bi->CommandLine32 = 0;
    g_bi->CommandLineCount = 0;

    printf("\n");

#if 0
    //
    // Drop SMAP entries above supported limit
    //
    for (int i = 0; i < g_bi->SmapCount; i++) {
        if (sm[i].type != Struct_Microsoft_Singularity_SMAPINFO_AddressTypeFree) {
            continue;
        }

        if ((sm[i].addr != 0ul) ||
            (sm[i].addr >= Class_Microsoft_Singularity_Hal_Platform_MAX_VIRTUAL_ADDR)) {
            sm[i] = sm[--g_bi->SmapCount];
        }
        else if (sm[i].addr + sm[i].size >= Class_Microsoft_Singularity_Hal_Platform_MAX_VIRTUAL_ADDR) {
            sm[i].size = Class_Microsoft_Singularity_Hal_Platform_MAX_VIRTUAL_ADDR - sm[i].addr;
        }
    }
#endif

    // Sort the system memory map.
    SortSmap(g_bi);

    //
    // Make a reasonable guess at the size of physical memory.
    //
    uint32 memoryKB = 0;
    for (int i = 0; i < g_bi->SmapCount; i++) {
        if (sm[i].type == Struct_Microsoft_Singularity_SMAPINFO_AddressTypeFree) {
            memoryKB += (uint32)(sm[i].size / 1024);
        }
    }
    printf("Physical memory: %uMB\n", memoryKB / 1024);

    CheckSmap(g_bi);

    //
    // Find the flash image.
    //
    uintptr flash = 0;
    for (int i = 0; i < g_bi->SmapCount && flash == 0; i++) {
        if (sm[i].type == Struct_Microsoft_Singularity_SMAPINFO_AddressTypeFree ||
            sm[i].type == Struct_Microsoft_Singularity_SMAPINFO_AddressTypeReserved) {

            flash = FindFlashImage((uintptr)sm[i].addr,
                                   (uintptr)(sm[i].addr + sm[i].size));
        }
    }

    if (flash == 0) {
        printf("No valid flash image.\n");
        Halt();
    }

    //
    // Count the flash files and size the image.
    //
    uint nMaxImages = 0;
    g_bi->DumpAddr32 = flash;
    g_bi->DumpSize32 = SizeFlashImage(flash, nMaxImages);
    printf("Flash: %08x..%08x.\n",
           (uint32)g_bi->DumpAddr32,
           (uint32)(g_bi->DumpAddr32 + g_bi->DumpSize32));
    printf("Flash has %d files.\n", nMaxImages);

    //
    // Remember the flash files.
    //
    Struct_Microsoft_Singularity_Io_FileImage * files =
        (Struct_Microsoft_Singularity_Io_FileImage *)
        alloc(sizeof(Struct_Microsoft_Singularity_Io_FileImage) * nMaxImages);

    ProcessFlashImage(flash, files, nMaxImages);
    g_bi->FileImageTableBase32 = (uintptr)files;
    g_bi->FileImageTableEntries = nMaxImages;

#if LIEABOUTSMAP
    printf("\n");
    printf("Editing the SMAP to protect the dump area...\n");

    for (i = 0; i < g_bi->SmapCount; i++) {
        // Does this region straddle the start of the dump area?
        // if so, truncate it
        if (sm[i].type == 1 &&
            sm[i].addr < g_bi->DumpAddr32 &&
            sm[i].addr + sm[i].size > g_bi->DumpAddr32) {

            sm[i].size = g_bi->DumpAddr32 - sm[i].addr;
            printf("  %08x..%08x %d (truncated)\n",
                   (uint32)(sm[i].addr),
                   (uint32)(sm[i].addr + sm[i].size),
                   sm[i].type);
        }

        if (sm[i].type == 1 &&
            sm[i].addr >= g_bi->DumpAddr32) {

            sm[i].type = 2; // Arbitrary non-free value
            printf("  %08x..%08x %d (marked unavailable)\n",
                   (uint32)(sm[i].addr),
                   (uint32)(sm[i].addr + sm[i].size),
                   sm[i].type);
        }
    }
    // Sort the system memory map.
    SortSmap(g_bi);
#endif

    uintptr kernelBase;
    g_bi->KernelDllSize = SizeOfPeImage(files[0].Address, kernelBase);
    printf("Kernel: %08x..%08x\n",
           g_bi->KernelDllBase,
           g_bi->KernelDllBase + g_bi->KernelDllSize);

    uintptr kernelEntry = ExpandPeImage(g_bi->KernelDllBase, files[0].Address);
    printf("Kernel Entry: %08x\n", kernelEntry);

    //
    g_bi->MpCpuCount         = 0;
    g_bi->MpStartupLock32 = (uintptr)&MpStartupLock;

    //printf("MpStartupLock32* %x, value %x\n", g_bi->MpStartupLock32, MpStartupLock);

    //
    // Set the offset to the context pointers, which are the
    // first two pointer words allocated in the page.
    //
    //
    // Allocate pages for commonly referenced data
    //

    uint8 * cpuRecord = (uint8 *)allocpages(2);

    //
    // Set the offset to the context pointers, which are the
    // first two pointer words allocated in the page.
    //
    g_bi->CpuRecordPointerOffset = 0 * sizeof(uintptr);
    g_bi->ThreadRecordPointerOffset = 1 * sizeof(uintptr);

    //
    // Set the DS relative address to the ProcessorContext
    //
    // Set our base for storing our actual X86.ProcessorContext
    //
    SetTpidrurw((uintptr)cpuRecord);

    // Align CpuRecord to 16-bytes after CpuRecord & ThreadRecord pointers.
    g_ci->CpuRecordPage = (uint32)cpuRecord + 16;

    g_bi->MiniDumpBase = (uintptr)g_bi->DumpAddr32;
    g_bi->MiniDumpLimit = g_bi->MiniDumpBase + ((g_bi->DumpSize32 + 0xffff) & 0xffff0000);

    //
    // Move to next phase
    //
    Class_Microsoft_Singularity_Hal_Platform  *bi = g_bi;
    Class_Microsoft_Singularity_Hal_Cpu *ci = g_ci;
    void (* pfHal)(void *, void *) = (void (*)(void *, void *))kernelEntry;

    g_bi->IsaCsns = (uint32)videoBuffer;
    g_bi->IsaReadPort = videoCursor;
    g_bi->KillAction = 0xffff;

    pfHal((void*)g_bi, (void*)g_ci);

    videoCursor = g_bi->IsaReadPort;

    printf("\n");
    printf("Kernel exited: %04x\n", g_bi->KillAction);
    g_bi->BootCount++;

    Halt();
    for(;;);
}

extern "C" unsigned __int64 __rt_udiv64by64( unsigned __int64 x, unsigned __int64 y)
{
    unsigned __int64 q = 0;
    unsigned __int64 mask = 1;
    if (y == 0) {
        return (unsigned __int64)-1;
    }

    while (y <= x) {
        if (y & 0x8000000000000000) {
            x -= y;
            q += mask;
            break;
        }
        mask <<= 1;
        y <<= 1;
    }

    while (mask !=0) {
        if (y <= x) {
            q += mask;
            x -= y;
        }
        y >>= 1;
        mask >>= 1;
    }

    return q;
}
