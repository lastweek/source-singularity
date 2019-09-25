//////////////////////////////////////////////////////////////////////////////////////////////////
//
// Microsoft Research Singularity
//
// Copyright (c) Microsoft Corporation.  All rights reserved.
//
// Header file for C++ intrinsics
//

#pragma once

////////////////////////////////////////////////////////////////////////////////////////////////////
// Non-portable intrinsics
////////////////////////////////////////////////////////////////////////////////////////////////////

// This section contains definitions of compiler intrinsics. This header file provides a
// uniform place where they can be declared if necessary.
//
// The intention here is to give as broad expressibility as possible to C++ code, without
// having to resort to assembly.  Thus platform-specific intrinsics are just fine.
//
// These functions were farmed out of the VS compiler header "intern.h", and then trimmed
// to limit dependencies on crt.
//
// Note that there is also a desire to build a platform layer of intrinsic-like functionalty,
// where certain platforms may have to manufacture the functionatity if necessary.
// Rather than do this at the C++ level, instead we do this at the managed level in Isal.Intrinsics.

extern "C" {

// All VS platforms

int __cdecl abs(int);
unsigned short __cdecl _byteswap_ushort(unsigned short value);
unsigned long __cdecl _byteswap_ulong(unsigned long value);
unsigned __int64 __cdecl _byteswap_uint64(unsigned __int64 value);
long __cdecl labs(long);
unsigned long __cdecl _lrotl(unsigned long,int);
unsigned long __cdecl _lrotr(unsigned long,int);
int __cdecl memcmp(const void *,const void *,size_t);
void * __cdecl memcpy(void *,const void *,size_t);
void * __cdecl memset(void *,int,size_t);
unsigned int __cdecl _rotl(unsigned int,int);
unsigned int __cdecl _rotr(unsigned int,int);
char * __cdecl strcat(char *,const char *);
int __cdecl strcmp(const char *,const char *);
char * __cdecl strcpy(char *,const char *);
size_t __cdecl strlen(const char *);
char * __cdecl _strset(char *,int);
char * __cdecl strset(char *,int);
unsigned __int64 __cdecl _rotl64(unsigned __int64,int);
unsigned __int64 __cdecl _rotr64(unsigned __int64,int);
__int64 __cdecl _abs64(__int64);

long _InterlockedExchange(long volatile *, long);

#if ISA_IX86 || ISA_IX64

// All IA32 platforms

void __cdecl __debugbreak(void);
void __cdecl _disable(void);
__int64 __emul(int,int);
unsigned __int64 __emulu(unsigned int,unsigned int);
void __cdecl _enable(void);
long __cdecl _InterlockedDecrement(long volatile *);
long _InterlockedExchangeAdd(long volatile *, long);
long _InterlockedCompareExchange (long volatile *, long, long);
__int64 _InterlockedCompareExchange64(__int64 volatile *, __int64, __int64);
long __cdecl _InterlockedIncrement(long volatile *);
int __cdecl _inp(unsigned short);
int __cdecl inp(unsigned short);
unsigned long __cdecl _inpd(unsigned short);
unsigned long __cdecl inpd(unsigned short);
unsigned short __cdecl _inpw(unsigned short);
unsigned short __cdecl inpw(unsigned short);
unsigned __int64  __ll_lshift(unsigned __int64,int);
__int64  __ll_rshift(__int64,int);
int __cdecl _outp(unsigned short,int);
int __cdecl outp(unsigned short,int);
unsigned long __cdecl _outpd(unsigned short,unsigned long);
unsigned long __cdecl outpd(unsigned short,unsigned long);
unsigned short __cdecl _outpw(unsigned short,unsigned short);
unsigned short __cdecl outpw(unsigned short,unsigned short);
void * _ReturnAddress(void);
unsigned __int64 __ull_rshift(unsigned __int64,int);
void * _AddressOfReturnAddress(void);
void _WriteBarrier(void);
void _ReadWriteBarrier(void);
void __wbinvd(void);
void __invlpg(void*);
unsigned __int64 __readmsr(unsigned long);
void __writemsr(unsigned long, unsigned __int64);
unsigned __int64 __rdtsc(void);
void __movsb(unsigned char *, unsigned char const *, size_t);
void __movsw(unsigned short *, unsigned short const *, size_t);
void __movsd(unsigned long *, unsigned long const *, size_t);
unsigned char __inbyte(unsigned short Port);
unsigned short __inword(unsigned short Port);
unsigned long __indword(unsigned short Port);
void __outbyte(unsigned short Port, unsigned char Data);
void __outword(unsigned short Port, unsigned short Data);
void __outdword(unsigned short Port, unsigned long Data);
void __inbytestring(unsigned short Port, unsigned char *Buffer, unsigned long Count);
void __inwordstring(unsigned short Port, unsigned short *Buffer, unsigned long Count);
void __indwordstring(unsigned short Port, unsigned long *Buffer, unsigned long Count);
void __outbytestring(unsigned short Port, unsigned char *Buffer, unsigned long Count);
void __outwordstring(unsigned short Port, unsigned short *Buffer, unsigned long Count);
void __outdwordstring(unsigned short Port, unsigned long *Buffer, unsigned long Count);
unsigned int __getcallerseflags();
void __vmx_vmptrst(unsigned __int64 *);
void __vmx_vmptrst(unsigned __int64 *);
void __svm_clgi(void);
void __svm_invlpga(void*, int);
void __svm_skinit(int);
void __svm_stgi(void);
void __svm_vmload(size_t);
void __svm_vmrun(size_t);
void __svm_vmsave(size_t);
void __halt(void);
void __sidt(void*);
void __lidt(void*);
void __ud2(void);
void __nop(void);
void __stosb(unsigned char *, unsigned char, size_t);
void __stosw(unsigned short *,  unsigned short, size_t);
void __stosd(unsigned long *,  unsigned long, size_t);
unsigned char _interlockedbittestandset(long *a, long b);
unsigned char _interlockedbittestandreset(long *a, long b);
void __cpuid(int a[4], int b);
unsigned __int64 __readpmc(unsigned long a);
unsigned long __segmentlimit(unsigned long a);
void __int2c(void);

// All IA platforms

long _InterlockedOr(long volatile *, long);
char _InterlockedOr8(char volatile *, char);
short _InterlockedOr16(short volatile *, short);
long _InterlockedXor(long volatile *, long);
char _InterlockedXor8(char volatile *, char);
short _InterlockedXor16(short volatile *, short);
long _InterlockedAnd(long volatile *, long);
char _InterlockedAnd8(char volatile *, char);
short _InterlockedAnd16(short volatile *, short);
unsigned char _bittest(long const *a, long b);
unsigned char _bittestandset(long *a, long b);
unsigned char _bittestandreset(long *a, long b);
unsigned char _bittestandcomplement(long *a, long b);
unsigned char _BitScanForward(unsigned long* Index, unsigned long Mask);
unsigned char _BitScanReverse(unsigned long* Index, unsigned long Mask);
void _ReadBarrier(void);
unsigned char _rotr8(unsigned char value, unsigned char shift);
unsigned short _rotr16(unsigned short value, unsigned char shift);
unsigned char _rotl8(unsigned char value, unsigned char shift);
unsigned short _rotl16(unsigned short value, unsigned char shift);
short _InterlockedIncrement16(short volatile *Addend);
short _InterlockedDecrement16(short volatile *Addend);
short _InterlockedCompareExchange16(short volatile *Destination, short Exchange, short Comparand);
void __nvreg_save_fence(void);
void __nvreg_restore_fence(void);

#endif // ISA_IX86 || ISA_IX64

#if ISA_IX86

// x86 only

long _InterlockedAddLargeStatistic(__int64 volatile *, long);
unsigned long __readcr0(void);
unsigned long __readcr2(void);
unsigned long __readcr3(void);
unsigned long __readcr4(void);
unsigned long __readcr8(void);
void __writecr0(unsigned);
void __writecr3(unsigned);
void __writecr4(unsigned);
void __writecr8(unsigned);
unsigned __readdr(unsigned int);
void __writedr(unsigned int, unsigned);
unsigned __readeflags(void);
void __writeeflags(unsigned);
unsigned char __readfsbyte(unsigned long Offset);
unsigned short __readfsword(unsigned long Offset);
unsigned long __readfsdword(unsigned long Offset);
unsigned __int64 __readfsqword(unsigned long Offset);
void __writefsbyte(unsigned long Offset, unsigned char Data);
void __writefsword(unsigned long Offset, unsigned short Data);
void __writefsdword(unsigned long Offset, unsigned long Data);
void __writefsqword(unsigned long Offset, unsigned __int64 Data);

#endif // ISA_IX86

#if ISA_IX64

// x64 only

__int64 _InterlockedDecrement64(__int64 volatile *);
__int64 _InterlockedExchange64(__int64 volatile *, __int64);
void * _InterlockedExchangePointer(void * volatile *, void *);
__int64 _InterlockedExchangeAdd64(__int64 volatile *, __int64);
__int64 _InterlockedCompare64Exchange128(__int64 volatile *Destination, __int64 ExchangeHigh, __int64 ExchangeLow, __int64 Comparand);
__int64 _InterlockedCompare64Exchange128_acq(__int64 volatile *Destination, __int64 ExchangeHigh, __int64 ExchangeLow, __int64 Comparand);
__int64 _InterlockedCompare64Exchange128_rel(__int64 volatile *Destination, __int64 ExchangeHigh, __int64 ExchangeLow, __int64 Comparand);
void *_InterlockedCompareExchangePointer (void * volatile *, void *, void *);
__int64 _InterlockedIncrement64(__int64 volatile *);
void __faststorefence(void);
__int64 __mulh(__int64,__int64);
unsigned __int64 __umulh(unsigned __int64,unsigned __int64);
unsigned __int64 __readcr0(void);
unsigned __int64 __readcr2(void);
unsigned __int64 __readcr3(void);
unsigned __int64 __readcr4(void);
unsigned __int64 __readcr8(void);
void __writecr0(unsigned __int64);
void __writecr3(unsigned __int64);
void __writecr4(unsigned __int64);
void __writecr8(unsigned __int64);
unsigned __int64 __readdr(unsigned int);
void __writedr(unsigned int, unsigned __int64);
unsigned __int64 __readeflags(void);
void __writeeflags(unsigned __int64);
void __movsq(unsigned long long *, unsigned long long const *, size_t);
unsigned char __readgsbyte(unsigned long Offset);
unsigned short __readgsword(unsigned long Offset);
unsigned long __readgsdword(unsigned long Offset);
unsigned __int64 __readgsqword(unsigned long Offset);
void __writegsbyte(unsigned long Offset, unsigned char Data);
void __writegsword(unsigned long Offset, unsigned short Data);
void __writegsdword(unsigned long Offset, unsigned long Data);
void __writegsqword(unsigned long Offset, unsigned __int64 Data);
unsigned char __vmx_vmclear(unsigned __int64*);
unsigned char __vmx_vmlaunch(void);
unsigned char __vmx_vmptrld(unsigned __int64*);
unsigned char __vmx_vmread(size_t, size_t*);
unsigned char __vmx_vmresume(void);
unsigned char __vmx_vmwrite(size_t, size_t);
unsigned char __vmx_on(unsigned __int64*);
void __stosq(unsigned __int64 *,  unsigned __int64, size_t);
unsigned char _interlockedbittestandset64(__int64 *a, __int64 b);
unsigned char _interlockedbittestandreset64(__int64 *a, __int64 b);
short _InterlockedCompareExchange16_np(short volatile *Destination, short Exchange, short Comparand);
long _InterlockedCompareExchange_np (long *, long, long);
__int64 _InterlockedCompareExchange64_np(__int64 *, __int64, __int64);
void *_InterlockedCompareExchangePointer_np (void **, void *, void *);
__int64 _InterlockedCompare64Exchange128_np(__int64 *Destination, __int64 ExchangeHigh, __int64 ExchangeLow, __int64 Comparand);
__int64 _InterlockedCompare64Exchange128_acq_np(__int64 *Destination, __int64 ExchangeHigh, __int64 ExchangeLow, __int64 Comparand);
__int64 _InterlockedCompare64Exchange128_rel_np(__int64 *Destination, __int64 ExchangeHigh, __int64 ExchangeLow, __int64 Comparand);
long _InterlockedAnd_np(long *, long);
char _InterlockedAnd8_np(char *, char);
short _InterlockedAnd16_np(short *, short);
__int64 _InterlockedAnd64_np(__int64 *, __int64);
long _InterlockedOr_np(long *, long);
char _InterlockedOr8_np(char *, char);
short _InterlockedOr16_np(short *, short);
__int64 _InterlockedOr64_np(__int64 *, __int64);
long _InterlockedXor_np(long *, long);
char _InterlockedXor8_np(char *, char);
short _InterlockedXor16_np(short *, short);
__int64 _InterlockedXor64_np(__int64 *, __int64);

// x64 + IA64

__int64 _InterlockedOr64(__int64 volatile *, __int64);
__int64 _InterlockedXor64(__int64 volatile *, __int64);
__int64 _InterlockedXor64(__int64 volatile *, __int64);
__int64 _InterlockedAnd64(__int64 volatile *, __int64);
unsigned char _bittest64(__int64 const *a, __int64 b);
unsigned char _bittestandset64(__int64 *a, __int64 b);
unsigned char _bittestandreset64(__int64 *a, __int64 b);
unsigned char _bittestandcomplement64(__int64 *a, __int64 b);
unsigned char _BitScanForward64(unsigned long* Index, unsigned __int64 Mask);
unsigned char _BitScanReverse64(unsigned long* Index, unsigned __int64 Mask);
unsigned __int64 __shiftleft128(unsigned __int64 LowPart, unsigned __int64 HighPart, unsigned char Shift);
unsigned __int64 __shiftright128(unsigned __int64 LowPart, unsigned __int64 HighPart, unsigned char Shift);
unsigned __int64 _umul128(unsigned __int64 multiplier, unsigned __int64 multiplicand, unsigned __int64 *highproduct);
__int64 _mul128(__int64 multiplier, __int64 multiplicand, __int64 *highproduct);

#endif // ISA_IX64

#if ISA_ARM

int __cdecl _MoveFromCoprocessor(unsigned int coproc, unsigned int opcode1, unsigned int crn, unsigned int crm, unsigned int opcode2);
int __cdecl _MoveFromCoprocessor2(unsigned int coproc, unsigned int opcode1, unsigned int crn, unsigned int crm, unsigned int opcode2);

void __cdecl _MoveToCoprocessor(unsigned int value, unsigned int coproc, unsigned int opcode1, unsigned int crn, unsigned int crm, unsigned int opcode2);
void __cdecl _MoveToCoprocessor2(unsigned int value, unsigned int coproc, unsigned int opcode1, unsigned int crn, unsigned int crm, unsigned int opcode2);

void __cdecl __emit(const unsigned __int32 opcode);
#define __debugbreak()  __emit(0xefffff03)

#endif // ISA_ARM
}


////////////////////////////////////////////////////////////////////////////////////////////////////
// Portable intrinsics
////////////////////////////////////////////////////////////////////////////////////////////////////

// This section contains standardized "intrinsics" which are portable across all architectures.
// In general we should keep this kind of thing to a minimum - the proper place to build a
// portablity layer at the managed level.

////////////////////////////////////////////////////////////////////////////////////////////////////
// Interlocked operations

extern "C" long InterlockedDecrement(long volatile *);
extern "C" long InterlockedExchange(long volatile *, long);
extern "C" long InterlockedExchangeAdd(long volatile *, long);
extern "C" long InterlockedCompareExchange (long volatile *, long, long);
extern "C" __int64 InterlockedCompareExchange64(__int64 volatile *, __int64, __int64);
extern "C" long InterlockedIncrement(long volatile *);

#if ISA_IX64 || ISA_IX86

#define InterlockedIncrement              _InterlockedIncrement
#define InterlockedDecrement              _InterlockedDecrement
#define InterlockedExchange               _InterlockedExchange
#define InterlockedExchangeAdd            _InterlockedExchangeAdd
#define InterlockedCompareExchange        _InterlockedCompareExchange
#define InterlockedCompareExchange64      _InterlockedCompareExchange64

#elif ISA_ARM

#define InterlockedExchange               _InterlockedExchange

#endif

// Map Pointer version to either 32 or 64 bit version
// (even though we have an explicit pointer version intrinsic on some isas.)

#if PTR_SIZE_32
#define InterlockedCompareExchangePointer(a,b,c) \
  ((void*)InterlockedCompareExchange((long volatile *)(a),(long)(b),(long)(c)))
#else
#define InterlockedCompareExchangePointer(a,b,c) \
  ((void*)InterlockedCompareExchange64((__int64 volatile *)(a),(__int64)(b),(__int64)(c)))
#endif

////////////////////////////////////////////////////////////////////////////////////////////////////
// General-use cheap cpu-relative timestamp

unsigned __int64 RDTSC(void);

#if ISA_IX64 || ISA_IX86

#define RDTSC           __rdtsc

#endif

