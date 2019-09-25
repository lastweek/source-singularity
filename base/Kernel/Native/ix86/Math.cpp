////////////////////////////////////////////////////////////////////////////////
//
//  Microsoft Research Singularity
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
//  File:   Math.cpp
//
//  Note:
//

#define LITTL_ENDIAN

#include "hal.h"

#pragma warning(disable: 4725)

//////////////////////////////////////////////////////////////////////////////
//
#define IMCW_EM         0x003f          // interrupt Exception Masks
#define IEM_INVALID     0x0001          //   invalid
#define IEM_DENORMAL    0x0002          //   denormal
#define IEM_ZERODIVIDE  0x0004          //   zero divide
#define IEM_OVERFLOW    0x0008          //   overflow
#define IEM_UNDERFLOW   0x0010          //   underflow
#define IEM_PRECISION   0x0020          //   precision

#define IMCW_RC         0x0c00          // Rounding Control
#define IRC_CHOP        0x0c00          //   chop
#define IRC_UP          0x0800          //   up
#define IRC_DOWN        0x0400          //   down
#define IRC_NEAR        0x0000          //   near

#define ISW_INVALID     0x0001          // invalid
#define ISW_DENORMAL    0x0002          // denormal
#define ISW_ZERODIVIDE  0x0004          // zero divide
#define ISW_OVERFLOW    0x0008          // overflow
#define ISW_UNDERFLOW   0x0010          // underflow
#define ISW_PRECISION   0x0020          // inexact

#define IMCW_PC         0x0300          // Precision Control
#define IPC_24          0x0000          //    24 bits
#define IPC_53          0x0200          //    53 bits
#define IPC_64          0x0300          //    64 bits

//////////////////////////////////////////////////////////////////////////////
//
#ifdef BIG_ENDIAN
// big endian
#define D_EXP(x) ((unsigned short *)&(x))
#define D_HI(x) ((unsigned long *)&(x))
#define D_LO(x) ((unsigned long *)&(x)+1)
#else
#define D_EXP(x) ((unsigned short *)&(x)+3)
#define D_HI(x) ((unsigned long *)&(x)+1)
#define D_LO(x) ((unsigned long *)&(x))
#endif

#define D_BIASM1 0x3fe // off by one to compensate for the implied bit
#define MAXEXP 1024
#define MINEXP -1021

// return the int representation of the exponent
// if x = .f * 2^n, 0.5<=f<1, return n (unbiased)
// e.g. INTEXP(3.0) == 2
#define INTEXP(x) ((signed short)((*D_EXP(x) & 0x7ff0) >> 4) - D_BIASM1)


// check for infinity, NAN
#define D_ISINF(x) ((*D_HI(x) & 0x7fffffff) == 0x7ff00000 && *D_LO(x) == 0)
#define IS_D_SPECIAL(x) ((*D_EXP(x) & 0x7ff0) == 0x7ff0)
#define IS_D_NAN(x) (IS_D_SPECIAL(x) && !D_ISINF(x))

#define IS_D_QNAN(x)    ((*D_EXP(x) & 0x7ff8) == 0x7ff8)
#define IS_D_SNAN(x)    ((*D_EXP(x) & 0x7ff8) == 0x7ff0 && \
                         (*D_HI(x) << 13 || *D_LO(x)))

#define IS_D_DENORM(x)  ((*D_EXP(x) & 0x7ff0) == 0  && \
                         (*D_HI(x) << 12 || *D_LO(x)))

#define IS_D_INF(x)  (*D_HI(x) == 0x7ff00000 && *D_LO(x) == 0)
#define IS_D_MINF(x) (*D_HI(x) == 0xfff00000 && *D_LO(x) == 0)

/////////////////////////////////////////////////////// Define special values.
//
typedef union {
    uint64  lng;
    float64 dbl;
} _dbl;

static _dbl _d_pos_inf = { 0x7ff0000000000000 };    // positive infinity
static _dbl _d_neg_inf = { 0xfff0000000000000 };    // negative infinity
static _dbl _d_ind     = { 0xfff8000000000000 };    // real indefinite
static _dbl _d_neg_zer = { 0x8000000000000000 };    // negative zero

//////////////////////////////////////////////////////////////////////////////
//

__declspec(naked) uint16 __fastcall g_ClearFp()
{
    __asm {
        push ebp
        mov ebp, esp

        // Save the old SW
        fnstsw [esp-4];
        fnclex
        mov eax, [esp-4];
        and eax, 0xffff;

        pop ebp;
        ret; // Returns result in EAX
    }
}

// Doesn't alter any additional registers
__declspec(naked) uint16 __fastcall g_ControlFp(uint16 newctrl, uint16 mask)
{
    (void)newctrl; (void)mask;  // accessed directly via ecx, edx respectively.
    __asm {
        push ebp
        mov ebp, esp

        // Save the old CW
        fstcw [esp-4];
        mov eax, [esp-4];
        and eax, 0xffff;

        // Load the new CW
        and ecx,edx;
        not edx;
        and edx,eax;
        or  edx,ecx;
        mov [esp-4], edx;
        fldcw [esp-4];

        pop ebp
        ret;
    }
}

// Doesn't alter any additional registers
__declspec(naked) void __fastcall g_RestoreFp(uint16 newctrl)
{
    (void)newctrl;  // accessed directly via ecx.
    __asm {
        push ebp
        mov ebp, esp

        // Load the new CW
        and ecx, 0xffff;
        mov [esp-4], ecx;
        fldcw [esp-4];

        pop ebp
        ret;
    }
}

//////////////////////////////////////////////////////////////////////////////
//
static float64 __fastcall _frnd(float64 v)
{
    _asm {
        fld v;
        frndint;
    }
}

static int32 __fastcall _ftoi(float64 v)
{
    int32 intval;
    int32 oldcw;
    int32 newcw;
    _asm {
        fstcw [oldcw];      // get control word

        mov eax, [oldcw];   // round mode saved
        or  eax, IRC_CHOP;  // set chop rounding mode
        mov [newcw], eax;   // back to memory

        fldcw [newcw];      // reset rounding
        fld v;
        fistp [intval];     // store chopped integer
        fwait;
        fldcw [oldcw];      // restore rounding
    }
    return intval;
}

static float64 _abs(float64 x)
{
    (*(uint64 *)&x) &= 0x7fffffffffffffff;
    return x;
}

static float64 _set_exp(float64 x, int exp) // does not check validity of exp
{
    float64 retval = x;
    int biased_exp = exp + D_BIASM1;
    *D_EXP(retval) = (unsigned short) (*D_EXP(x) & 0x800f | (biased_exp << 4));
    return retval;
}

int _get_exp(float64 x)
{
    signed short exp;
    exp = (signed short)((*D_EXP(x) & 0x7ff0) >> 4);
    exp -= D_BIASM1; //unbias
    return (int) exp;
}


//  Provide the mantissa and  the exponent of e^x
//
//  Entry:
//     x : a (non special) float64 precision number
//
//  Exit:
//     *newexp: the exponent of e^x
//     return value: the mantissa m of e^x scaled by a factor
//                   (the value of this factor has no significance.
//                    The mantissa can be obtained with _set_exp(m, 0).
//
//     _set_exp(m, *pnewexp) may be used for constructing the final
//     result, if it is within the representable range.
//
static inline float64 r_exp_p(float64 z)
{
    static float64 const p0 = 0.249999999999999993e+0;
    static float64 const p1 = 0.694360001511792852e-2;
    static float64 const p2 = 0.165203300268279130e-4;

    return ( (p2 * (z) + p1) * (z) + p0 );
}

static inline float64 r_exp_q(float64 z)
{
    static float64 const q0 = 0.500000000000000000e+0;
    static float64 const q1 = 0.555538666969001188e-1;
    static float64 const q2 = 0.495862884905441294e-3;

    return ( (q2 * (z) + q1) * (z) + q0 );
}

float64 _exphlp(float64 x, int * pnewexp)
{
    static float64 const  LN2INV =  1.442695040889634074;      // 1/ln(2)
    static float64 const  C1     =  0.693359375000000000;
    static float64 const  C2     = -2.1219444005469058277e-4;
    float64 xn;
    float64 g,z,gpz,qz,rg;
    int n;

    xn = _frnd(x * LN2INV);
    n = _ftoi(xn);

    // assume guard digit is present
    g = (x - xn * C1) - xn * C2;
    z = g*g;
    gpz = g * r_exp_p(z);
    qz = r_exp_q(z);
    rg = 0.5 + gpz/(qz-gpz);

    n++;

    *pnewexp = _get_exp(rg) + n;
    return rg;
}

//
// Decompose a number to a normalized mantissa and exponent.
//
static float64 _decomp(float64 x, int *pexp)
{
    int exp;
    float64 man;

    if (x == 0.0) {
        man = 0.0;
        exp = 0;
    }
    else if (IS_D_DENORM(x)) {
        int neg;

        exp = 1 - D_BIASM1;
        neg = x < 0.0;
        while((*D_EXP(x) & 0x0010) == 0) {
            // shift mantissa to the left until bit 52 is 1
            (*D_HI(x)) <<= 1;
            if (*D_LO(x) & 0x80000000)
                (*D_HI(x)) |= 0x1;
            (*D_LO(x)) <<= 1;
            exp--;
        }
        (*D_EXP(x)) &= 0xffef; // clear bit 52
        if (neg) {
            (*D_EXP(x)) |= 0x8000; // set sign bit
        }
        man = _set_exp(x,0);
    }
    else {
        man = _set_exp(x,0);
        exp = INTEXP(x);
    }

    *pexp = exp;
    return man;
}

static bool is_odd_integer(float64 y)
{
    int exp = INTEXP(y);
    if (exp < 1 || exp > 63) {
        return false;
    }
    return(((*(uint64*)&y) | 0x10000000000000u) << (10 + exp) == 0x8000000000000000);
}

static bool is_even_integer(float64 y)
{
    int exp = INTEXP(y);
    if (exp < 1 || exp > 63) {
        return false;
    }
    return (((*(uint64*)&y) | 0x10000000000000u) << (10 + exp) == 0);
}

//////////////////////////////////////////////////////////////////////////////

float64 Class_System_Math::g_Atan2(float64 v, float64 w)
{
    __asm {
        fld v;
        fld w;
        fpatan;
    }
}

float64 Class_System_Math::g_Abs(float64 v)
{
    __asm {
        fld v;
        fabs;
    }
}

float64 Class_System_Math::g_Sqrt(float64 v)
{
    __asm {
        fld v;
        fsqrt;
    }
}

float64 Class_System_Math::g_Log10(float64 v)
{
    __asm {
        fld v;
        fldlg2;
        fxch ST(1);
        fyl2x; // Returns result in ST(0)
    }
}

float64 Class_System_Math::g_Exp(float64 v)
{
    __asm {
        fldl2e;
        fmul v;
        fld ST(0);
        frndint;
        fxch ST(1);
        fsub ST(0), ST(1);
        f2xm1;
        fld1;
        faddp ST(1), ST(0);
        fscale;
        fstp ST(1); // Returns result in ST(0)
    }
}

// constants for the rational approximation
static inline float64 r_sinh_p(float64 f)
{
    static float64 const p0 = -0.35181283430177117881e+6;
    static float64 const p1 = -0.11563521196851768270e+5;
    static float64 const p2 = -0.16375798202630751372e+3;
    static float64 const p3 = -0.78966127417357099479e+0;

    return (((p3 * (f) + p2) * (f) + p1) * (f) + p0);
}

static inline float64 r_sinh_q(float64 f)
{
    static float64 const q0 = -0.21108770058106271242e+7;
    static float64 const q1 =  0.36162723109421836460e+5;
    static float64 const q2 = -0.27773523119650701667e+3;
    // q3 = 1 is not used (avoid multiplication by 1)

    return ((((f) + q2) * (f) + q1) * (f) + q0);
}

// Compute the hyperbolic sine of a number.
//  The algorithm (reduction / rational approximation) is
// taken from Cody & Waite.
float64 Class_System_Math::g_Sinh(float64 v)
{
    static float64 const EPS  = 5.16987882845642297e-26;    // 2^(-53) / 2
    // exp(YBAR) should be close to but less than XMAX
    // and 1/exp(YBAR) should not underflow
    static float64 const YBAR = 7.00e2;

    // WMAX=ln(OVFX)+0.69 (Cody & Waite),omitted LNV, used OVFX instead of BIGX

    static float64 const WMAX = 1.77514678223345998953e+003;

    float64 result;

    if (IS_D_SPECIAL(v)) {
        if (IS_D_INF(v) || IS_D_MINF(v)) {
        }
        else if (IS_D_QNAN(v)) {
            // TODO: should throw a soft exception.
        }
        else if (IS_D_SNAN(v)) {
            // TODO: should throw a hard exception.
        }
        result = v;
    }
    else if (v == 0.0) {
        // no precision exception
        result = v;
    }
    else {
        bool neg = (v < 0.0);
        float64 y = _abs(v);

        if (y > 1.0) {
            int newexp;
            if (y > YBAR) {
                if (y > WMAX) {
                    // result too large, even after scaling
                    result = v * _d_pos_inf.dbl;
                    // TODO: should through hard exception.
                    goto exit;
                }

                //
                // result = exp(y)/2
                //

                result = _exphlp(y, &newexp);
                newexp --;      //divide by 2
                if (newexp > MAXEXP) {
                    result = 0.0; //result = _set_exp(result, newexp-IEEE_ADJUST);
                    // TODO: should through hard exception.
                    goto exit;
                }
                else {
                    result = _set_exp(result, newexp);
                }

            }
            else {
                float64 z = _exphlp(y, &newexp);
                z = _set_exp(z, newexp);
                result = (z - 1.0/z) / 2.0;
            }

            if (neg) {
                result = -result;
            }
        }
        else {
            if (y < EPS) {
                result = v;
                if (IS_D_DENORM(result)) {
                    result = 0.0; // result = _add_exp(result, IEEE_ADJUST);
                    // TODO: should through hard exception.
                    goto exit;
                }
            }
            else {
                float64 f = v * v;
                float64 r = f * (r_sinh_p(f) / r_sinh_q(f));
                result = v + v * r;
            }
        }
    }

  exit:
    return result;
}

//  Compute the hyperbolic cosine of a number.
//  The algorithm (reduction / rational approximation) is
//  taken from Cody & Waite.
//
float64 Class_System_Math::g_Cosh(float64 v)
{
    // exp(YBAR) should be close to but less than XMAX
    // and 1/exp(YBAR) should not underflow
    static float64 const YBAR = 7.00e2;

    // WMAX=ln(OVFX)+0.69 (Cody & Waite),omitted LNV, used OVFX instead of BIGX
    static float64 const WMAX = 1.77514678223345998953e+003;

    float64 result;

    if (IS_D_SPECIAL(v)) {
        if (IS_D_INF(v) || IS_D_MINF(v)) {
            result = _d_pos_inf.dbl;

        }
        else if (IS_D_QNAN(v)) {
            // TODO: should throw a soft exception.
            result = v;
        }
        else {
            // TODO: should throw a hard exception.
            result = v;
        }
    }
    else if (v == 0.0) {
        result = 1.0;
    }
    else {
        float64 y = _abs(v);
        if (y > YBAR) {
            if (y > WMAX) {
                // TODO: should throw a hard exception.
                result = v;
                goto exit;
            }

            //
            // result =     exp(y)/2
            //

            int newexp;
            result = _exphlp(y, &newexp);
            newexp --;          //divide by 2
            if (newexp > MAXEXP) {
                // TODO: should throw a hard exception.
                result = 0.0; //result = _set_exp(result, newexp-IEEE_ADJUST);
                goto exit;
            }
            else {
                result = _set_exp(result, newexp);
            }
        }
        else {
            int newexp;
            float64 z = _exphlp(y, &newexp);
            z = _set_exp(z, newexp);
            result = (z + 1.0/z) / 2.0;
        }
        // TODO: should throw a hard exception if exactness is required.
    }

  exit:
    return result;
}

// Compute the hyperbolic tangent of a number.
// The algorithm (reduction / rational approximation) is
// taken from Cody & Waite.

static inline float64 r_tanh(float64 g)
{
    // constants for rational approximation
    static float64 const p0 = -0.16134119023996228053e+4;
    static float64 const p1 = -0.99225929672236083313e+2;
    static float64 const p2 = -0.96437492777225469787e+0;
    static float64 const q0 =  0.48402357071988688686e+4;
    static float64 const q1 =  0.22337720718962312926e+4;
    static float64 const q2 =  0.11274474380534949335e+3;
    static float64 const q3 =  0.10000000000000000000e+1;

    return ((((p2 * (g) + p1) * (g) + p0) * (g)) / ((((g) + q2) * (g) + q1) * (g) + q0));
}

float64 Class_System_Math::g_Tanh(float64 v)
{
    // constants
    static float64 const EPS  = 5.16987882845642297e-26;     // 2^(-53) / 2
    static float64 const XBIG = 1.90615474653984960096e+001; // ln(2)(53+2)/2
    static float64 const C0   = 0.54930614433405484570;      // ln(3)/2

    if (IS_D_SPECIAL(v)) {
        if (IS_D_INF(v)) {
            v = 1.0;
        }
        else if (IS_D_MINF(v)) {
            v = -1.0;
        }
        else if (IS_D_QNAN(v)) {
            // TODO: should throw a soft exception.
        }
        else if (IS_D_SNAN(v)) {
            // TODO: should throw a hard exception.
        }
    }
    else if (v == 0.0) {
        // no precision exception
    }
    else {
        bool neg = false;
        if (v < 0.0) {
            neg = true;
            v = -v;
        }

        if (v > XBIG) {
            v = 1;
        }
        else if (v > C0) {
            v = 0.5 - 1.0 / (g_Exp(v+v) + 1.0);
            v = v + v;
        }
        else if (v < EPS) {
            if (IS_D_DENORM(v)) {
                // TODO: should throw a heard exception.
            }
        }
        else {
            v = v + v * r_tanh(v * v);
        }
        if (neg) {
            v = -v;
        }
    }
    return v;
}

float64 Class_System_Math::g_Acos(float64 v)
{
    __asm {
        fld v;
        fld1;               // load 1.0
        fadd st, st(1);     // 1+x
        fld1;               // load 1.0
        fsub st, st(2);     // 1-x
        fmul;               // (1+x)(1-x)
        fsqrt;              // sqrt((1+x)(1-x))
        fxch;
        fpatan;             // fpatan(x,sqrt((1+x)(1-x)))
    }
}

float64 Class_System_Math::g_Asin(float64 v)
{
    __asm {
        fld v;
        fld1;               // load 1.0
        fadd st, st(1);     // 1+x
        fld1;               // load 1.0
        fsub st, st(2);     // 1-x
        fmul;               // (1+x)(1-x)
        fsqrt;              // sqrt((1+x)(1-x))
        fpatan;             // fpatan(x,sqrt((1+x)(1-x)))
    }
}

static float64 _fastpow(float64 v, float64 w)
{
    __asm {
        fld w;              // neither v or w can be a boundary cases.
        fld v;
        fyl2x;              // compute y*log2(x)
        fld st(0);          // duplicate stack top
        frndint;            // N = round(y)
        fsubr st(1), st;
        fxch;
        fchs;               // g = y - N where abs(g) < 1
        f2xm1;              // 2**g - 1
        fld1;
        fadd;               // 2**g
        fscale;             // (2**g) * (2**N) - gives 2**y
        fstp st(1);         // pop extra stuff from fp stack
    }
}

float64 Class_System_Math::g_Pow(float64 v, float64 w)
{
    float64 result = 0.0;

    // check for infinity or NAN
    if (IS_D_SPECIAL(w) || IS_D_SPECIAL(v)) {
        if (IS_D_INF(w)) {
            float64 absv = _abs(v);
            if (absv > 1.0) {
                result = _d_pos_inf.dbl;
            }
            else if (absv < 1.0) {
                result = 0.0;
            }
            else {
                result = _d_ind.dbl;
                // TODO: Should throw a hard exception.
                goto exit;
            }
        }
        else if (IS_D_MINF(w)) {
            float64 absv = _abs(v);
            if (absv > 1.0) {
                result = 0.0;
            }
            else if (absv < 1.0) {
                result = _d_pos_inf.dbl;
            }
            else {
                result = _d_ind.dbl;
                // TODO: Should throw a hard exception.
                goto exit;
            }
        }
        else if (IS_D_INF(v)) {
            if (w > 0.0) {
                result = _d_pos_inf.dbl;
            }
            else if (w < 0.0) {
                result = 0.0;
            }
            else {
                result = 1.0;
            }
        }
        else if (IS_D_MINF(v)) {
            if (w > 0.0) {
                result = is_odd_integer(w) ? _d_neg_inf.dbl : _d_pos_inf.dbl;
            }
            else if (w < 0.0) {
                result = is_odd_integer(w) ? _d_neg_zer.dbl : 0.0;
            }
            else {
                result = 1.0;
            }
        }
    }
    else if (w == 0.0) {
        result = 1.0;
    }
    else if (v == 0.0) {
        if (w < 0.0) {
            // TODO: Should throw a hard exception.
            result = is_odd_integer(v) ? _d_neg_inf.dbl : _d_pos_inf.dbl;
        }
        else {
            result = is_odd_integer(v) ? w : 0.0;
        }
    }
    else if (v < 0.0) {
        if (is_odd_integer(w)) {
            result = - _fastpow(-v, w);
        }
        else if (is_even_integer(w)) {
            result = _fastpow(-v, w);
        }
        else {
            // TODO: Should throw a hard exception.
            result = v;
        }
    }
    else {
        result = _fastpow(v, w);
    }

  exit:
    return result;
}

float64 Class_System_Math::g_Mod(float64 x, float64 y)
{
    float64 result = 0.0;

    // check for infinity or NAN
    if (IS_D_SPECIAL(y) || IS_D_SPECIAL(x)) {
        if (IS_D_SNAN(y) || IS_D_SNAN(x)) {
            // TODO: Should throw a hard exception.
        }
        else if (IS_D_QNAN(y) || IS_D_QNAN(x)) {
            // TODO: Should throw a soft exception.
            result = x;
        }
        else if (IS_D_INF(x) || IS_D_MINF(x)) {
            // TODO: Should throw a hard exception.
        }
    }
    else if (y == 0.0) {
        // TODO: Should throw a hard exception.
    }
    else if (x == 0.0) {
        result = x;
    }
    else {
        const int SCALE = 53;
        bool neg = false;
        bool denorm = false;
        float64 d,ty,fx,fy;
        int nx, ny, nexp;

        if (x < 0.0) {
            result = -x;
            neg = 1;
        }
        else {
            result = x;
        }

        ty = _abs(y);

        while (result >= ty) {
            fx = _decomp(result, &nx);
            fy = _decomp(ty, &ny);

            if (nx < MINEXP) {
                // result is a denormalized number
                denorm = true;
                nx += SCALE;
                ny += SCALE;
                result = _set_exp(fx, nx);
                ty = _set_exp(fy, ny);
            }


            if (fx >= fy) {
                nexp = nx ;
            }
            else {
                nexp = nx - 1;
            }
            d = _set_exp(fy, nexp);
            result -= d;
        }
        if (denorm) {
            // TODO: should raise only FP_U exception.
        }
        if (neg) {
            result = -result;
        }
    }

    return result;
}

//
///////////////////////////////////////////////////////////////// End of File.

