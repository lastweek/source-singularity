////////////////////////////////////////////////////////////////////////////////
//
//  Microsoft Research Singularity
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
//  File:   Number.cpp
//
//  Note:   Kernel & Process
//

#include "hal.h"

//////////////////////////////////////////////////////////////////////////////
//
extern "C" int _fltused = 0x9875;

//////////////////////////////////////////////////////////////////////////////
//
#define LITTLE_ENDIAN

#if defined(_M_MRX000) || defined(_M_ALPHA) || defined(_M_PPC) || defined(_M_IA64)
#define REQUIRES_UNALIGNED_FLAG
#endif

//////////////////////////////////////////////////////////////////////////////
//
static const int32 SCALE_NAN = (int32)0x80000000;
static const int32 SCALE_INF = 0x7FFFFFFF;

//  Currently our string conversion routines do not conform to the special
//  requirements of the IEEE standard for floating point conversions.
//  We do this to avoid IEEE exceptions.

#pragma pack(4)
typedef struct {
        uint8 ld12[12];
} _LDBL12;
#pragma pack()

#define PTR_12(x) ((uint8 *)(&(x)->ld12))

#define MAX_USHORT  ((uint16)0xffff)
#define MSB_USHORT  ((uint16)0x8000)
#define MAX_ULONG   ((uint32)0xffffffff)
#define MSB_ULONG   ((uint32)0x80000000)

#define LD_BIAS     0x3fff  // exponent bias for long double
#define LD_BIASM1   0x3ffe  // LD_BIAS - 1
#define LD_MAXEXP   0x7fff  // maximum biased exponent

#define D_BIAS      0x3ff   // exponent bias for double
#define D_BIASM1    0x3fe   // D_BIAS - 1
#define D_MAXEXP    0x7ff   // maximum biased exponent

#define _IS_MAN_INF(signbit, manhi, manlo) ((manhi)==MSB_ULONG && (manlo)==0x0 )

#if defined (LITTLE_ENDIAN)

// Manipulation of a 12-byte long double number (an ordinary
// 10-byte long double plus two extra bytes of mantissa).
//
// byte layout:
//
//              +--+--+--+--+--+--+--+--+--+--+--+--+
//              |XT:2 |  MANLO:4  |  MANHI:4  |EXP:2|
//              +--+--+--+--+--+--+--+--+--+--+--+--+
//              |  UL_LO:4  |  UL_MED:4 |  UL_HI:4  |
//              +--+--+--+--+--+--+--+--+--+--+--+--+
//
#define U_EXP_12(p) ((uint16 *)(PTR_12(p)+10))      // exponent/sign
#if !defined(REQUIRES_UNALIGNED_FLAG)
#define UL_MANHI_12(p) ((uint32 *)(PTR_12(p)+6))    // 4 hi-order bytes of ord mantissa
#define UL_MANLO_12(p) ((uint32 *)(PTR_12(p)+2))    // 4 lo-order bytes of ord mantissa
#else
#define UL_MANHI_12(p) ((uint32  __unaligned *) (PTR_12(p)+6) )
#define UL_MANLO_12(p) ((uint32  __unaligned *) (PTR_12(p)+2) )
#endif // defined(REQUIRES_UNALIGNED_FLAG)
#define U_XT_12(p) ((uint16 *)PTR_12(p))            // 2 extra-lo bytes of mantissa

#define UL_LO_12(p) ((uint32 *)PTR_12(p))           // 4 lo-order bytes of 12-byte value
#define UL_MED_12(p) ((uint32 *)(PTR_12(p)+4))      // 4 mid-order bytes of 12-byte value
#define UL_HI_12(p) ((uint32 *)(PTR_12(p)+8))       // 4 hi-order bytes of 12-byte value

#define UCHAR_12(p,i) ((uint8 *)PTR_12(p)+(i))      // byte of order i (LSB=0)
#define USHORT_12(p,i) ((uint16 *)((uint8 *)PTR_12(p)+(i))) // uint16 at byte of order i
#define ULONG_12(p,i) ((uint32 *)((uint8 *)PTR_12(p)+(i)))  // uint32 at byte of order i

// Manipulation of a 64bit IEEE double
#define UINT164_D(p) ((uint16 *)(p) + 3)
#define UL_HI_D(p) ((uint32 *)(p) + 1)
#define UL_LO_D(p) ((uint32 *)(p))

#endif // defined(LITTLE_ENDIAN)

#if defined (BIG_ENDIAN)

#define U_EXP_12(p) ((uint16 *)PTR_12(p))
#define UL_MANHI_12(p) ((uint32 *)(PTR_12(p)+2))
#define UL_MANLO_12(p) ((uint32 *)(PTR_12(p)+6))
#define U_XT_12(p) ((uint16 *)(PTR_12(p)+10))

#define UL_LO_12(p) ((uint32 *)(PTR_12(p)+8))
#define UL_MED_12(p) ((uint32 *)(PTR_12(p)+4))
#define UL_HI_12(p) ((uint32 *)PTR_12(p))

#define UCHAR_12(p,i) ((uint8 *)PTR_12(p)+(11-(i)))
#define USHORT_12(p,i)  ((uint16 *)((uint8 *)PTR_12(p)+10-(i)))
#define ULONG_12(p,i) ((uint32 *)((uint8 *)PTR_12(p)+8-(i)))

// Manipulation of a 64bit IEEE double
#define UINT164_D(p) ((uint16 *)(p))
#define UL_HI_D(p) ((uint32 *)(p))
#define UL_LO_D(p) ((uint32 *)(p) + 1)

#endif // defined(BIG_ENDIAN)

#define PUT_INF_12(p,sign) \
                  *UL_HI_12(p) = (sign)?0xffff8000:0x7fff8000; \
                  *UL_MED_12(p) = 0; \
                  *UL_LO_12(p) = 0;

#define PUT_ZERO_12(p) *UL_HI_12(p) = 0; \
                  *UL_MED_12(p) = 0; \
                  *UL_LO_12(p) = 0;

#define ISZERO_12(p) ((*UL_HI_12(p)&0x7fffffff) == 0 && \
                      *UL_MED_12(p) == 0 && \
                      *UL_LO_12(p) == 0 )

//////////////////////////////////////////////////////////////////////////////
//
//  Purpose:  Convert a double into a _LDBL12
//
//  Entry: double *px
//
//  Exit: the corresponding _LDBL12 value is returned in *pld
//
static void dtold12(_LDBL12 *pld, const double *px)
{
    uint32 msb = MSB_ULONG;
    uint16 ldexp = 0;
    uint16 exp = (*UINT164_D(px) & (uint16)0x7ff0) >> 4;
    uint16 sign = *UINT164_D(px) & (uint16)0x8000;
    uint32 manhi = *UL_HI_D(px) & 0xfffff;
    uint32 manlo = *UL_LO_D(px);

    switch (exp) {
      case D_MAXEXP:
        ldexp = LD_MAXEXP;
        break;
      case 0:
        // check for zero
        if (manhi == 0 && manlo == 0) {
            *UL_MANHI_12(pld) = 0;
            *UL_MANLO_12(pld) = 0;
            *U_XT_12(pld) = 0;
            *U_EXP_12(pld) = 0;
            return;
        }
        // we have a denormal -- we'll normalize later
        ldexp = (uint16) ((int16)exp - D_BIAS + LD_BIAS + 1);
        msb = 0;
        break;
      default:
        exp -= D_BIAS;
        ldexp = (uint16) ((int16)exp + LD_BIAS);
        break;
    }

    *UL_MANHI_12(pld) = msb | (manhi << 11) | (manlo >> 21);
    *UL_MANLO_12(pld) = manlo << 11;

    // normalize if necessary
    while ((*UL_MANHI_12(pld) & MSB_ULONG) == 0) {
        // shift left
        *UL_MANHI_12(pld) = (*UL_MANHI_12(pld) << 1) |
            (MSB_ULONG & *UL_MANLO_12(pld) ? 1: 0);
        (*UL_MANLO_12(pld)) <<= 1;
        ldexp --;
    }
    *U_EXP_12(pld) = sign | ldexp;
    *U_XT_12(pld) = 0;
}

//////////////////////////////////////////////////////////////////////////////
//
//  Purpose: add two uint32 numbers and return carry
//
//  Entry: uint32 x, uint32 y : the numbers to be added
//         uint32 *sum : where to store the result
//
//  Exit: *sum receives the value of x+y
//        the value of the carry is returned
//
static int addl(uint32 x, uint32 y, uint32 *sum)
{
    uint32 r = x + y;
    *sum = r;
    return (r < x || r < y);
}

//////////////////////////////////////////////////////////////////////////////
//
//  Purpose: add two _LDBL12 numbers. The numbers are added
//  as 12-byte integers. Overflow is ignored.
//
//  Entry: x,y: pointers to the operands
//
//  Exit: *x receives the sum
//
static void add_12(_LDBL12 *x, _LDBL12 *y)
{
    if (addl(*UL_LO_12(x),*UL_LO_12(y),UL_LO_12(x))) {
        if (addl(*UL_MED_12(x),(uint32)1,UL_MED_12(x))) {
            (*UL_HI_12(x))++;
        }
    }
    if (addl(*UL_MED_12(x),*UL_MED_12(y),UL_MED_12(x))) {
        (*UL_HI_12(x))++;
    }
    // ignore next carry -- assume no overflow will occur
    (void)addl(*UL_HI_12(x),*UL_HI_12(y),UL_HI_12(x));
}

//////////////////////////////////////////////////////////////////////////////
//
//  Purpose: Shift a _LDBL12 number one bit to the left (right). The number
//  is shifted as a 12-byte integer. The MSB is lost.
//
//  Entry: x: a pointer to the operand
//
//  Exit: *x is shifted one bit to the left (or right)
//
static void shl_12(_LDBL12 *p)
{
    uint32 c0 = (*UL_LO_12(p) & MSB_ULONG) ? 1: 0;
    uint32 c1 = (*UL_MED_12(p) & MSB_ULONG) ? 1: 0;
    *UL_LO_12(p) <<= 1;
    *UL_MED_12(p) = (*UL_MED_12(p) << 1) | c0;
    *UL_HI_12(p) = (*UL_HI_12(p) << 1) | c1;
}

static void shr_12(_LDBL12 *p)
{
    uint32 c2 = (*UL_HI_12(p) & 0x1) ? MSB_ULONG: 0;
    uint32 c1 = (*UL_MED_12(p) & 0x1) ? MSB_ULONG: 0;
    *UL_HI_12(p) >>= 1;
    *UL_MED_12(p) = (*UL_MED_12(p) >> 1) | c2;
    *UL_LO_12(p) = (*UL_LO_12(p) >> 1) | c1;
}

//////////////////////////////////////////////////////////////////////////////
//
//  Purpose: multiply two _LDBL12 numbers
//
//  Entry: px,py: pointers to the _LDBL12 operands
//
//  Exit: *px contains the product
//
static void ld12mul(_LDBL12 *px, _LDBL12 *py)
{
    _LDBL12 tempman; // this is actually a 12-byte mantissa, not a 12-byte long double

    *UL_LO_12(&tempman) = 0;
    *UL_MED_12(&tempman) = 0;
    *UL_HI_12(&tempman) = 0;

    uint16 expx = *U_EXP_12(px);
    uint16 expy = *U_EXP_12(py);
    uint16 sign = (expx ^ expy) & (uint16)0x8000;
    expx &= 0x7fff;
    expy &= 0x7fff;
    uint16 expsum = expx + expy;
    if (expx >= LD_MAXEXP
        || expy >= LD_MAXEXP
        || expsum > LD_MAXEXP + LD_BIASM1) {
        // overflow to infinity
        PUT_INF_12(px,sign);
        return;
    }
    if (expsum <= LD_BIASM1 - 63) {
        // underflow to zero
        PUT_ZERO_12(px);
        return;
    }
    if (expx == 0) {
        // If this is a denormal temp real then the mantissa
        // was shifted right once to set bit 63 to zero.
        expsum++; // Correct for this
        if (ISZERO_12(px)) {
            // put positive sign
            *U_EXP_12(px) = 0;
            return;
        }
    }
    if (expy == 0) {
        expsum++; // because arg2 is denormal
        if (ISZERO_12(py)) {
            PUT_ZERO_12(px);
            return;
        }
    }

    int roffs = 0;
    for (int i = 0; i < 5; i++) {
        int poffs = i << 1;
        int qoffs = 8;
        for (int j = 5 - i; j > 0; j--) {
            uint32 prod;
            int carry;
            uint16 *p, *q;
            uint32 *r;
            p = USHORT_12(px,poffs);
            q = USHORT_12(py,qoffs);
            r = ULONG_12(&tempman,roffs);
            prod = (uint32)*p * (uint32)*q;
            carry = addl(*r,prod,r);
            if (carry) {
                // roffs should be less than 8 in this case
                (*USHORT_12(&tempman,roffs+4))++;
            }
            poffs += 2;
            qoffs -= 2;
        }
        roffs += 2;
    }

    expsum -= LD_BIASM1;

    // normalize
    while ((int16)expsum > 0 &&
           ((*UL_HI_12(&tempman) & MSB_ULONG) == 0)) {
        shl_12(&tempman);
        expsum--;
    }

    if ((int16)expsum <= 0) {
        bool sticky = false;
        expsum--;
        while ((int16)expsum < 0) {
            if (*U_XT_12(&tempman) & 0x1) {
                sticky = true;
            }
            shr_12(&tempman);
            expsum++;
        }
        if (sticky) {
            *U_XT_12(&tempman) |= 0x1;
        }
    }

    if (*U_XT_12(&tempman) > 0x8000 ||
        ((*UL_LO_12(&tempman) & 0x1ffff) == 0x18000)) {
        // round up
        if (*UL_MANLO_12(&tempman) == MAX_ULONG) {
            *UL_MANLO_12(&tempman) = 0;
            if (*UL_MANHI_12(&tempman) == MAX_ULONG) {
                *UL_MANHI_12(&tempman) = 0;
                if (*U_EXP_12(&tempman) == MAX_USHORT) {
                    // 12-byte mantissa overflow
                    *U_EXP_12(&tempman) = MSB_USHORT;
                    expsum++;
                }
                else {
                    (*U_EXP_12(&tempman))++;
                }
            }
            else {
                (*UL_MANHI_12(&tempman))++;
            }
        }
        else {
            (*UL_MANLO_12(&tempman))++;
        }
    }

    // check for exponent overflow
    if (expsum >= 0x7fff) {
        PUT_INF_12(px, sign);
        return;
    }

    // put result in px
    *U_XT_12(px) = *USHORT_12(&tempman,2);
    *UL_MANLO_12(px) = *UL_MED_12(&tempman);
    *UL_MANHI_12(px) = *UL_HI_12(&tempman);
    *U_EXP_12(px) = expsum | sign;
}

static void multtenpow12(_LDBL12 *pld12, int pow)
{
    //////////////////////////////////////////////////////////////////////////////
    //
    // Format: A 10 byte long double + 2 bytes of extra precision
    // If the extra precision is desired, the 10-byte long double
    // should be "unrounded" first.
    //
    static _LDBL12 _pow10pos[] = {
#if defined(LITTLE_ENDIAN)
        {{0x00,0x00, 0x00,0x00,0x00,0x00,0x00,0x00,0x00,0xA0,0x02,0x40}},   // P0001
        {{0x00,0x00, 0x00,0x00,0x00,0x00,0x00,0x00,0x00,0xC8,0x05,0x40}},   // P0002
        {{0x00,0x00, 0x00,0x00,0x00,0x00,0x00,0x00,0x00,0xFA,0x08,0x40}},   // P0003
        {{0x00,0x00, 0x00,0x00,0x00,0x00,0x00,0x00,0x40,0x9C,0x0C,0x40}},   // P0004
        {{0x00,0x00, 0x00,0x00,0x00,0x00,0x00,0x00,0x50,0xC3,0x0F,0x40}},   // P0005
        {{0x00,0x00, 0x00,0x00,0x00,0x00,0x00,0x00,0x24,0xF4,0x12,0x40}},   // P0006
        {{0x00,0x00, 0x00,0x00,0x00,0x00,0x00,0x80,0x96,0x98,0x16,0x40}},   // P0007
        {{0x00,0x00, 0x00,0x00,0x00,0x00,0x00,0x20,0xBC,0xBE,0x19,0x40}},   // P0008
        {{0x00,0x00, 0x00,0x00,0x00,0x04,0xBF,0xC9,0x1B,0x8E,0x34,0x40}},   // P0016
        {{0x00,0x00, 0x00,0xA1,0xED,0xCC,0xCE,0x1B,0xC2,0xD3,0x4E,0x40}},   // P0024
        {{0x20,0xF0, 0x9E,0xB5,0x70,0x2B,0xA8,0xAD,0xC5,0x9D,0x69,0x40}},   // P0032
        {{0xD0,0x5D, 0xFD,0x25,0xE5,0x1A,0x8E,0x4F,0x19,0xEB,0x83,0x40}},   // P0040
        {{0x71,0x96, 0xD7,0x95,0x43,0x0E,0x05,0x8D,0x29,0xAF,0x9E,0x40}},   // P0048
        {{0xF9,0xBF, 0xA0,0x44,0xED,0x81,0x12,0x8F,0x81,0x82,0xB9,0x40}},   // P0056
        {{0xBF,0x3C, 0xD5,0xA6,0xCF,0xFF,0x49,0x1F,0x78,0xC2,0xD3,0x40}},   // P0064
        {{0x6F,0xC6, 0xE0,0x8C,0xE9,0x80,0xC9,0x47,0xBA,0x93,0xA8,0x41}},   // P0128
        {{0xBC,0x85, 0x6B,0x55,0x27,0x39,0x8D,0xF7,0x70,0xE0,0x7C,0x42}},   // P0192
        {{0xBC,0xDD, 0x8E,0xDE,0xF9,0x9D,0xFB,0xEB,0x7E,0xAA,0x51,0x43}},   // P0256
        {{0xA1,0xE6, 0x76,0xE3,0xCC,0xF2,0x29,0x2F,0x84,0x81,0x26,0x44}},   // P0320
        {{0x28,0x10, 0x17,0xAA,0xF8,0xAE,0x10,0xE3,0xC5,0xC4,0xFA,0x44}},   // P0384
        {{0xEB,0xA7, 0xD4,0xF3,0xF7,0xEB,0xE1,0x4A,0x7A,0x95,0xCF,0x45}},   // P0448
        {{0x65,0xCC, 0xC7,0x91,0x0E,0xA6,0xAE,0xA0,0x19,0xE3,0xA3,0x46}},   // P0512
        {{0x0D,0x65, 0x17,0x0C,0x75,0x81,0x86,0x75,0x76,0xC9,0x48,0x4D}},   // P1024
        {{0x58,0x42, 0xE4,0xA7,0x93,0x39,0x3B,0x35,0xB8,0xB2,0xED,0x53}},   // P1536
        {{0x4D,0xA7, 0xE5,0x5D,0x3D,0xC5,0x5D,0x3B,0x8B,0x9E,0x92,0x5A}},   // P2048
        {{0xFF,0x5D, 0xA6,0xF0,0xA1,0x20,0xC0,0x54,0xA5,0x8C,0x37,0x61}},   // P2560
        {{0xD1,0xFD, 0x8B,0x5A,0x8B,0xD8,0x25,0x5D,0x89,0xF9,0xDB,0x67}},   // P3072
        {{0xAA,0x95, 0xF8,0xF3,0x27,0xBF,0xA2,0xC8,0x5D,0xDD,0x80,0x6E}},   // P3584
        {{0x4C,0xC9, 0x9B,0x97,0x20,0x8A,0x02,0x52,0x60,0xC4,0x25,0x75}}    // P4096
#endif
#if defined(BIG_ENDIAN)
        {{0x40,0x02,0xA0,0x00,0x00,0x00,0x00,0x00,0x00,0x00, 0x00,0x00}},   // P0001
        {{0x40,0x05,0xC8,0x00,0x00,0x00,0x00,0x00,0x00,0x00, 0x00,0x00}},   // P0002
        {{0x40,0x08,0xFA,0x00,0x00,0x00,0x00,0x00,0x00,0x00, 0x00,0x00}},   // P0003
        {{0x40,0x0C,0x9C,0x40,0x00,0x00,0x00,0x00,0x00,0x00, 0x00,0x00}},   // P0004
        {{0x40,0x0F,0xC3,0x50,0x00,0x00,0x00,0x00,0x00,0x00, 0x00,0x00}},   // P0005
        {{0x40,0x12,0xF4,0x24,0x00,0x00,0x00,0x00,0x00,0x00, 0x00,0x00}},   // P0006
        {{0x40,0x16,0x98,0x96,0x80,0x00,0x00,0x00,0x00,0x00, 0x00,0x00}},   // P0007
        {{0x40,0x19,0xBE,0xBC,0x20,0x00,0x00,0x00,0x00,0x00, 0x00,0x00}},   // P0008
        {{0x40,0x34,0x8E,0x1B,0xC9,0xBF,0x04,0x00,0x00,0x00, 0x00,0x00}},   // P0016
        {{0x40,0x4E,0xD3,0xC2,0x1B,0xCE,0xCC,0xED,0xA1,0x00, 0x00,0x00}},   // P0024
        {{0x40,0x69,0x9D,0xC5,0xAD,0xA8,0x2B,0x70,0xB5,0x9E, 0xF0,0x20}},   // P0032
        {{0x40,0x83,0xEB,0x19,0x4F,0x8E,0x1A,0xE5,0x25,0xFD, 0x5D,0xD0}},   // P0040
        {{0x40,0x9E,0xAF,0x29,0x8D,0x05,0x0E,0x43,0x95,0xD7, 0x96,0x71}},   // P0048
        {{0x40,0xB9,0x82,0x81,0x8F,0x12,0x81,0xED,0x44,0xA0, 0xBF,0xF9}},   // P0056
        {{0x40,0xD3,0xC2,0x78,0x1F,0x49,0xFF,0xCF,0xA6,0xD5, 0x3C,0xBF}},   // P0064
        {{0x41,0xA8,0x93,0xBA,0x47,0xC9,0x80,0xE9,0x8C,0xE0, 0xC6,0x6F}},   // P0128
        {{0x42,0x7C,0xE0,0x70,0xF7,0x8D,0x39,0x27,0x55,0x6B, 0x85,0xBC}},   // P0192
        {{0x43,0x51,0xAA,0x7E,0xEB,0xFB,0x9D,0xF9,0xDE,0x8E, 0xDD,0xBC}},   // P0256
        {{0x44,0x26,0x81,0x84,0x2F,0x29,0xF2,0xCC,0xE3,0x76, 0xE6,0xA1}},   // P0320
        {{0x44,0xFA,0xC4,0xC5,0xE3,0x10,0xAE,0xF8,0xAA,0x17, 0x10,0x28}},   // P0384
        {{0x45,0xCF,0x95,0x7A,0x4A,0xE1,0xEB,0xF7,0xF3,0xD4, 0xA7,0xEB}},   // P0448
        {{0x46,0xA3,0xE3,0x19,0xA0,0xAE,0xA6,0x0E,0x91,0xC7, 0xCC,0x65}},   // P0512
        {{0x4D,0x48,0xC9,0x76,0x75,0x86,0x81,0x75,0x0C,0x17, 0x65,0x0D}},   // P1024
        {{0x53,0xED,0xB2,0xB8,0x35,0x3B,0x39,0x93,0xA7,0xE4, 0x42,0x58}},   // P1536
        {{0x5A,0x92,0x9E,0x8B,0x3B,0x5D,0xC5,0x3D,0x5D,0xE5, 0xA7,0x4D}},   // P2048
        {{0x61,0x37,0x8C,0xA5,0x54,0xC0,0x20,0xA1,0xF0,0xA6, 0x5D,0xFF}},   // P2560
        {{0x67,0xDB,0xF9,0x89,0x5D,0x25,0xD8,0x8B,0x5A,0x8B, 0xFD,0xD1}},   // P3072
        {{0x6E,0x80,0xDD,0x5D,0xC8,0xA2,0xBF,0x27,0xF3,0xF8, 0x95,0xAA}},   // P3584
        {{0x75,0x25,0xC4,0x60,0x52,0x02,0x8A,0x20,0x97,0x9B, 0xC9,0x4C}}    // P4096
#endif
    };

    static _LDBL12 _pow10neg[] = {
#if defined(LITTLE_ENDIAN)
        {{0xCD,0xCC, 0xCD,0xCC,0xCC,0xCC,0xCC,0xCC,0xCC,0xCC,0xFB,0x3F}},   // N0001
        {{0x71,0x3D, 0x0A,0xD7,0xA3,0x70,0x3D,0x0A,0xD7,0xA3,0xF8,0x3F}},   // N0002
        {{0x5A,0x64, 0x3B,0xDF,0x4F,0x8D,0x97,0x6E,0x12,0x83,0xF5,0x3F}},   // N0003
        {{0xC3,0xD3, 0x2C,0x65,0x19,0xE2,0x58,0x17,0xB7,0xD1,0xF1,0x3F}},   // N0004
        {{0xD0,0x0F, 0x23,0x84,0x47,0x1B,0x47,0xAC,0xC5,0xA7,0xEE,0x3F}},   // N0005
        {{0x40,0xA6, 0xB6,0x69,0x6C,0xAF,0x05,0xBD,0x37,0x86,0xEB,0x3F}},   // N0006
        {{0x33,0x3D, 0xBC,0x42,0x7A,0xE5,0xD5,0x94,0xBF,0xD6,0xE7,0x3F}},   // N0007
        {{0xC2,0xFD, 0xFD,0xCE,0x61,0x84,0x11,0x77,0xCC,0xAB,0xE4,0x3F}},   // N0008
        {{0x2F,0x4C, 0x5B,0xE1,0x4D,0xC4,0xBE,0x94,0x95,0xE6,0xC9,0x3F}},   // N0016
        {{0x92,0xC4, 0x53,0x3B,0x75,0x44,0xCD,0x14,0xBE,0x9A,0xAF,0x3F}},   // N0024
        {{0xDE,0x67, 0xBA,0x94,0x39,0x45,0xAD,0x1E,0xB1,0xCF,0x94,0x3F}},   // N0032
        {{0x24,0x23, 0xC6,0xE2,0xBC,0xBA,0x3B,0x31,0x61,0x8B,0x7A,0x3F}},   // N0040
        {{0x61,0x55, 0x59,0xC1,0x7E,0xB1,0x53,0x7C,0x12,0xBB,0x5F,0x3F}},   // N0048
        {{0xD7,0xEE, 0x2F,0x8D,0x06,0xBE,0x92,0x85,0x15,0xFB,0x44,0x3F}},   // N0056
        {{0x24,0x3F, 0xA5,0xE9,0x39,0xA5,0x27,0xEA,0x7F,0xA8,0x2A,0x3F}},   // N0064
        {{0x7D,0xAC, 0xA1,0xE4,0xBC,0x64,0x7C,0x46,0xD0,0xDD,0x55,0x3E}},   // N0128
        {{0x63,0x7B, 0x06,0xCC,0x23,0x54,0x77,0x83,0xFF,0x91,0x81,0x3D}},   // N0192
        {{0x91,0xFA, 0x3A,0x19,0x7A,0x63,0x25,0x43,0x31,0xC0,0xAC,0x3C}},   // N0256
        {{0x21,0x89, 0xD1,0x38,0x82,0x47,0x97,0xB8,0x00,0xFD,0xD7,0x3B}},   // N0320
        {{0xDC,0x88, 0x58,0x08,0x1B,0xB1,0xE8,0xE3,0x86,0xA6,0x03,0x3B}},   // N0384
        {{0xC6,0x84, 0x45,0x42,0x07,0xB6,0x99,0x75,0x37,0xDB,0x2E,0x3A}},   // N0448
        {{0x33,0x71, 0x1C,0xD2,0x23,0xDB,0x32,0xEE,0x49,0x90,0x5A,0x39}},   // N0512
        {{0xA6,0x87, 0xBE,0xC0,0x57,0xDA,0xA5,0x82,0xA6,0xA2,0xB5,0x32}},   // N1024
        {{0xE2,0x68, 0xB2,0x11,0xA7,0x52,0x9F,0x44,0x59,0xB7,0x10,0x2C}},   // N1536
        {{0x25,0x49, 0xE4,0x2D,0x36,0x34,0x4F,0x53,0xAE,0xCE,0x6B,0x25}},   // N2048
        {{0x8F,0x59, 0x04,0xA4,0xC0,0xDE,0xC2,0x7D,0xFB,0xE8,0xC6,0x1E}},   // N2560
        {{0x9E,0xE7, 0x88,0x5A,0x57,0x91,0x3C,0xBF,0x50,0x83,0x22,0x18}},   // N3072
        {{0x4E,0x4B, 0x65,0x62,0xFD,0x83,0x8F,0xAF,0x06,0x94,0x7D,0x11}},   // N3584
        {{0xE4,0x2D, 0xDE,0x9F,0xCE,0xD2,0xC8,0x04,0xDD,0xA6,0xD8,0x0A}}    // N4096
#endif
#if defined(BIG_ENDIAN)
        {{0x3F,0xFB,0xCC,0xCC,0xCC,0xCC,0xCC,0xCC,0xCC,0xCD, 0xCC,0xCD}},   // N0001
        {{0x3F,0xF8,0xA3,0xD7,0x0A,0x3D,0x70,0xA3,0xD7,0x0A, 0x3D,0x71}},   // N0002
        {{0x3F,0xF5,0x83,0x12,0x6E,0x97,0x8D,0x4F,0xDF,0x3B, 0x64,0x5A}},   // N0003
        {{0x3F,0xF1,0xD1,0xB7,0x17,0x58,0xE2,0x19,0x65,0x2C, 0xD3,0xC3}},   // N0004
        {{0x3F,0xEE,0xA7,0xC5,0xAC,0x47,0x1B,0x47,0x84,0x23, 0x0F,0xD0}},   // N0005
        {{0x3F,0xEB,0x86,0x37,0xBD,0x05,0xAF,0x6C,0x69,0xB6, 0xA6,0x40}},   // N0006
        {{0x3F,0xE7,0xD6,0xBF,0x94,0xD5,0xE5,0x7A,0x42,0xBC, 0x3D,0x33}},   // N0007
        {{0x3F,0xE4,0xAB,0xCC,0x77,0x11,0x84,0x61,0xCE,0xFD, 0xFD,0xC2}},   // N0008
        {{0x3F,0xC9,0xE6,0x95,0x94,0xBE,0xC4,0x4D,0xE1,0x5B, 0x4C,0x2F}},   // N0016
        {{0x3F,0xAF,0x9A,0xBE,0x14,0xCD,0x44,0x75,0x3B,0x53, 0xC4,0x92}},   // N0024
        {{0x3F,0x94,0xCF,0xB1,0x1E,0xAD,0x45,0x39,0x94,0xBA, 0x67,0xDE}},   // N0032
        {{0x3F,0x7A,0x8B,0x61,0x31,0x3B,0xBA,0xBC,0xE2,0xC6, 0x23,0x24}},   // N0040
        {{0x3F,0x5F,0xBB,0x12,0x7C,0x53,0xB1,0x7E,0xC1,0x59, 0x55,0x61}},   // N0048
        {{0x3F,0x44,0xFB,0x15,0x85,0x92,0xBE,0x06,0x8D,0x2F, 0xEE,0xD7}},   // N0056
        {{0x3F,0x2A,0xA8,0x7F,0xEA,0x27,0xA5,0x39,0xE9,0xA5, 0x3F,0x24}},   // N0064
        {{0x3E,0x55,0xDD,0xD0,0x46,0x7C,0x64,0xBC,0xE4,0xA1, 0xAC,0x7D}},   // N0128
        {{0x3D,0x81,0x91,0xFF,0x83,0x77,0x54,0x23,0xCC,0x06, 0x7B,0x63}},   // N0192
        {{0x3C,0xAC,0xC0,0x31,0x43,0x25,0x63,0x7A,0x19,0x3A, 0xFA,0x91}},   // N0256
        {{0x3B,0xD7,0xFD,0x00,0xB8,0x97,0x47,0x82,0x38,0xD1, 0x89,0x21}},   // N0320
        {{0x3B,0x03,0xA6,0x86,0xE3,0xE8,0xB1,0x1B,0x08,0x58, 0x88,0xDC}},   // N0384
        {{0x3A,0x2E,0xDB,0x37,0x75,0x99,0xB6,0x07,0x42,0x45, 0x84,0xC6}},   // N0448
        {{0x39,0x5A,0x90,0x49,0xEE,0x32,0xDB,0x23,0xD2,0x1C, 0x71,0x33}},   // N0512
        {{0x32,0xB5,0xA2,0xA6,0x82,0xA5,0xDA,0x57,0xC0,0xBE, 0x87,0xA6}},   // N1024
        {{0x2C,0x10,0xB7,0x59,0x44,0x9F,0x52,0xA7,0x11,0xB2, 0x68,0xE2}},   // N1536
        {{0x25,0x6B,0xCE,0xAE,0x53,0x4F,0x34,0x36,0x2D,0xE4, 0x49,0x25}},   // N2048
        {{0x1E,0xC6,0xE8,0xFB,0x7D,0xC2,0xDE,0xC0,0xA4,0x04, 0x59,0x8F}},   // N2560
        {{0x18,0x22,0x83,0x50,0xBF,0x3C,0x91,0x57,0x5A,0x88, 0xE7,0x9E}},   // N3072
        {{0x11,0x7D,0x94,0x06,0xAF,0x8F,0x83,0xFD,0x62,0x65, 0x4B,0x4E}},   // N3584
        {{0x0A,0xD8,0xA6,0xDD,0x04,0xC8,0xD2,0xCE,0x9F,0xDE, 0x2D,0xE4}}    // N4096
#endif
    };

    _LDBL12 *pow_10p = _pow10pos - 8;
    if (pow == 0) {
        return;
    }
    if (pow < 0) {
        pow = -pow;
        pow_10p = _pow10neg - 8;
    }

    while (pow) {
        pow_10p += 7;
        int last3 = pow & 0x7;  // the 3 LSBits of pow
        pow >>= 3;
        if (last3 == 0) {
            continue;
        }
        _LDBL12 *py = pow_10p + last3;

        // do an exact 12 byte multiplication
        if (*U_XT_12(py) >= 0x8000) {

            _LDBL12 unround = *py;      // copy number
            (*UL_MANLO_12(&unround))--; // unround adjacent byte
            py = &unround;              // point to new operand
        }
        ld12mul(pld12, py);
    }
}

//////////////////////////////////////////////////////////////////////////////
//
//  Purpose:
//      _ecvt converts value to a null terminated string of
//      UNICODE digits, and returns a pointer to the result.
//      The position of the decimal point relative to the
//      beginning of the string is stored indirectly through
//      decpt, where negative means to the left of the returned
//      digits.  If the sign of the result is negative, the
//      bool pointed to by negative is set to true, otherwise it is
//      false.  The low order digit is rounded.
//
//  Entry:
//      double value - number to be converted
//      int digits - number of digits after decimal point
//
//  Exit:
//      returns pointer to the character representation of value.
//      int *decpt - pointer to int with position of decimal point
//      bool *negative - pointer to bool for if value < 0.
//
bool Class_System_Number::g_ecvt(double value,
                                 int digits,
                                 ClassVector_bartok_char * buf,
                                 int *decpt,
                                 bool *negative)
{
    if ((uint32)digits > buf->length - 1) {
        digits = buf->length - 1;
    }
    bartok_char *man = buf->values;

    // useful constants (see algorithm explanation below)
    const uint16 log2hi = 0x4d10;
    const uint16 log2lo = 0x4d;
    const uint16 log4hi = 0x9a;
    const uint32 c = 0x134312f4;
#if defined(LITTLE_ENDIAN)
    _LDBL12 ld12_one_tenth = {
        {0xcc,0xcc,0xcc,0xcc,0xcc,0xcc,0xcc,0xcc,0xcc,0xcc,0xfb,0x3f}
    };
#endif
#if defined(BIG_ENDIAN)
    _LDBL12 ld12_one_tenth = {
        {0x3f,0xfb,0xcc,0xcc,0xcc,0xcc,0xcc,0xcc,0xcc,0xcc,0xcc,0xcc}
    };
#endif

    // convert the double into a 12-byte long double.
    _LDBL12 ld12;
    dtold12(&ld12, &value);

    uint16 expn = *U_EXP_12(&ld12);
    uint32 manhi = *UL_MANHI_12(&ld12);
    uint32 manlo = *UL_MANLO_12(&ld12);
    uint16 sign = expn & MSB_USHORT;
    expn &= 0x7fff;
    *U_EXP_12(&ld12) = expn;

    *negative = (sign != 0);

    if (expn == 0 && manhi == 0 && manlo == 0) {
      zero_fos:
        *decpt = 0;
        *negative = false;
        man[0] = '0';
        man[1] = '\0';
        return true;
    }

    if (expn == 0x7fff) {
        man[0] = '\0';
        *decpt = SCALE_NAN;
        if (_IS_MAN_INF(sign, manhi, manlo)) {
            *decpt = SCALE_INF; // infinity
        }
        return false;
    }
    else {
        // * Algorithm for the decoding of a valid real number x *
        //
        // In the following INT(r) is the largest integer less than or
        // equal to r (i.e. r rounded toward -infinity). We want a result
        // r equal to 1 + log(x), because then x = mantissa
        // * 10^(INT(r)) so that .1 <= mantissa < 1.  Unfortunately,
        // we cannot compute s exactly so we must alter the procedure
        // slightly.  We will instead compute an estimate r of 1 +
        // log(x) which is always low.  This will either result
        // in the correctly normalized number on the top of the stack
        // or perhaps a number which is a factor of 10 too large.  We
        // will then check to see that if x is larger  than one
        // and if so multiply x by 1/10.
        //
        // We will use a low precision (fixed point 24 bit) estimate
        // of of 1 + log base 10 of x.  We have approximately .mm
        // * 2^hhll on the top of the stack where m, h, and l represent
        // hex digits, mm represents the high 2 hex digits of the
        // mantissa, hh represents the high 2 hex digits of the exponent,
        // and ll represents the low 2 hex digits of the exponent.  Since
        // .mm is a truncated representation of the mantissa, using it
        // in this monotonically increasing  polynomial approximation
        // of the logarithm will naturally give a low result. Let's
        // derive a formula for a lower bound r on 1 + log(x):
        //
        //      .4D104D42H < log(2)=.30102999...(base 10) < .4D104D43H
        //     .9A20H < log(4)=.60205999...(base 10) < .9A21H
        //
        //  1/2 <= .mm < 1
        //  ==>  log(.mm) >= .mm * log(4) - log(4)
        //
        // Substituting in truncated hex constants in the formula above
        // gives r = 1 + .4D104DH * hhll. + .9AH * .mm - .9A21H.  Now
        // multiplication of hex digits 5 and 6 of log(2) by ll has an
        // insignificant effect on the first 24 bits of the result so
        // it will not be calculated.  This gives the expression r =
        // 1 + .4D10H * hhll. + .4DH * .hh + .9A * .mm - .9A21H.
        // Finally we must add terms to our formula to subtract out the
        // effect of the exponent bias.  We obtain the following formula:
        //
        //           (implied decimal point)
        //   <                 >.<                  >
        //   |3|3|2|2|2|2|2|2|2|2|2|2|1|1|1|1|1|1|1|1|1|1|0|0|0|0|0|0|0|0|0|0|
        //   |1|0|9|8|7|6|5|4|3|2|1|0|9|8|7|6|5|4|3|2|1|0|9|8|7|6|5|4|3|2|1|0|
        // + <         1       >
        // + <               .4D10H * hhll.             >
        // +                 <       .00004DH * hh00.       >
        // +                 <          .9AH * .mm      >
        // -                 <        .9A21H        >
        // - <               .4D10H * 3FFEH             >
        // -                 <       .00004DH * 3F00H       >
        //
        //  ==>  r = .4D10H * hhll. + .4DH * .hh + .9AH * .mm - 1343.12F4H
        //
        // The difference between the lower bound r and the upper bound
        // s is calculated as follows:
        //
        //  .937EH < 1/ln(10)-log(1/ln(4))=.57614993...(base 10) < .937FH
        //
        //  1/2 <= .mm < 1
        //  ==>  log(.mm) <= .mm * log(4) - [1/ln(10) - log(1/ln(4))]
        //
        // so tentatively s = r + log(4) - [1/ln(10) - log(1/ln(4))],
        // but we must also add in terms to ensure we will have an upper
        // bound even after the truncation of various values.  Because
        // log(2) * hh00. is truncated to .4D104DH * hh00.  we must
        // add .0043H, because log(2) * ll. is truncated to .4D10H *
        // ll. we must add .0005H, because <mantissa> * log(4) is
        // truncated to .mm * .9AH we must add .009AH and .0021H.
        //
        // Thus s = r - .937EH + .9A21H + .0043H + .0005H + .009AH + .0021H
        //   = r + .07A6H
        //  ==>  s = .4D10H * hhll. + .4DH * .hh + .9AH * .mm - 1343.0B4EH
        //
        // r is equal to 1 + log(x) more than (10000H - 7A6H) /
        // 10000H = 97% of the time.
        //
        // In the above formula, a uint32 is use to accommodate r, and
        // there is an implied decimal point in the middle.

        uint16 hh = expn >> 8;
        uint16 ll = expn & (uint16)0xff;
        uint16 mm = (uint16) (manhi >> 24);   // the two most significant bytes of the mantissa.
        int32 r = (int32)log2hi*(int32)expn + log2lo*hh + log4hi*mm - c;
        // the corresponding power of 10
        int32 ir = (int16)(r >> 16); // ir = floor(r)

        // We stated that we wanted to normalize x so that
        //
        //  .1 <= x < 1
        //
        // This was a slight oversimplification.  Actually we want a
        // number which when rounded to 16 significant digits is in the
        // desired range.  To do this we must normalize x so that
        //
        //  .1 - 5*10^(-18) <= x < 1 - 5*10^(-17)
        //
        // and then round.
        //
        // If we had f = INT(1+log(x)) we could multiply by 10^(-f)
        // to get x into the desired range.  We do not quite have
        // f but we do have INT(r) from the last step which is equal
        // to f 97% of the time and 1 less than f the rest of the time.
        // We can multiply by 10^-[INT(r)] and if the result is greater
        // than 1 - 5*10^(-17) we can then multiply by 1/10.  This final
        // result will lie in the proper range.

        // multiply by 10^(-ir)
        multtenpow12(&ld12,-ir);

        // if ld12 >= 1.0 then divide by 10.0
        if (*U_EXP_12(&ld12) >= 0x3fff) {
            ir++;
            ld12mul(&ld12,&ld12_one_tenth);
        }

        *decpt = ir;

        int ub_exp = *U_EXP_12(&ld12) - 0x3ffe; // unbias exponent
        *U_EXP_12(&ld12) = 0;

        // Now the mantissa has to be converted to fixed point.
        // Then we will use the MSB of ld12 for generating
        // the decimal digits. The next 11 bytes will hold
        // the mantissa (after it has been converted to
        // fixed point).

        for (int i = 0; i < 8; i++) {
            shl_12(&ld12);
            // make space for an extra byte, in case we shift right later.
        }
        if (ub_exp < 0) {
            int shift_count = (-ub_exp) & 0xff;
            for (; shift_count > 0; shift_count--) {
                shr_12(&ld12);
            }
        }

        bartok_char *p = man;
        for (int digcount = digits + 1; digcount > 0; digcount--) {
            _LDBL12 tmp12 = ld12;
            shl_12(&ld12);
            shl_12(&ld12);
            add_12(&ld12,&tmp12);
            shl_12(&ld12);    // ld12 *= 10

            // Now we have the first decimal digit in the most significant byte of exponent
            *p++ = (char) (*UCHAR_12(&ld12,11) + '0');
            *UCHAR_12(&ld12,11) = 0;
        }

        bartok_char round = *(--p);
        p--;
        // p points now to the last character of the string excluding the rounding digit.
        if (round >= '5') {
            // look for a non-9 digit starting from the end of string
            for (; p >= man && *p == '9'; p--) {
                *p = '0';
            }
            if (p < man) {
                p++;
                (*decpt)++;
            }
            (*p)++;
        }
        else {
            // We probably don't want to truncate all of the zeros!
            for (; p >= man && *p == '0'; p--) {
                // remove extra zeros;
            }
            if (p < man) {
                goto zero_fos;
            }
        }
        man[(p - man + 1)] = '\0';
        return true;
    }
}

double Class_System_Number::g_atof(struct ClassVector_uint8 *a)
{
    Assert(!"atof");
    return 0;
}
//
///////////////////////////////////////////////////////////////// End of File.
