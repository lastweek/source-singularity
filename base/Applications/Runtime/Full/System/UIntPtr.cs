// ==++==
//
//   Copyright (c) Microsoft Corporation.  All rights reserved.
//
// ==--==

namespace System
{

    using System;
    using System.Globalization;
    using System.Runtime.CompilerServices;

    //| <include path='docs/doc[@for="UIntPtr"]/*' />
    [CLSCompliant(false)]
    [NoCCtor]
    public struct UIntPtr : IFormattable
    {
        unsafe private void* m_value;

        //| <include path='docs/doc[@for="UIntPtr.Zero"]/*' />
        [Intrinsic]
        public static readonly UIntPtr Zero;

        //| <include path='docs/doc[@for="UIntPtr.MaxValue"]/*' />
        [Intrinsic]
        public static readonly UIntPtr MaxValue;

        //| <include path='docs/doc[@for="UIntPtr.Size"]/*' />
        [Intrinsic]
        public static readonly int Size;

        //| <include path='docs/doc[@for="UIntPtr.UIntPtr"]/*' />
        [Intrinsic]
        [NoHeapAllocation]
        public extern UIntPtr(uint value);

        [Intrinsic]
        [NoHeapAllocation]
        public extern UIntPtr(int value);

        //| <include path='docs/doc[@for="UIntPtr.UIntPtr1"]/*' />
        [Intrinsic]
        [NoHeapAllocation]
        public extern UIntPtr(ulong value);

        //| <include path='docs/doc[@for="UIntPtr.UIntPtr2"]/*' />
        [CLSCompliant(false)]
        [Intrinsic]
        [NoHeapAllocation]
        public extern unsafe UIntPtr(void* value);

        //| <include path='docs/doc[@for="UIntPtr.Equals"]/*' />
        [Inline]
        public unsafe override bool Equals(Object obj)
        {
            if (obj is UIntPtr) {
                return (m_value == ((UIntPtr)obj).m_value);
            }
            else {
                return false;
            }
        }

        //| <include path='docs/doc[@for="UIntPtr.GetHashCode"]/*' />
        [Inline]
        public unsafe override int GetHashCode()
        {
            return (int)m_value & 0x7fffffff;
        }

        //| <include path='docs/doc[@for="UIntPtr.ToUInt32"]/*' />
        [Intrinsic]
        [NoHeapAllocation]
        public extern uint ToUInt32();

        //| <include path='docs/doc[@for="UIntPtr.ToUInt64"]/*' />
        [Intrinsic]
        [NoHeapAllocation]
        public extern ulong ToUInt64();

        //| <include path='docs/doc[@for="UIntPtr.ToString"]/*' />
        [Inline]
        public unsafe override String ToString()
        {
            if (sizeof(UIntPtr) == 4) {
                return this.ToUInt32().ToString();
            }
            else {
                return this.ToUInt64().ToString();
            }
        }

        [Inline]
        public unsafe String ToString(String format)
        {
            if (sizeof(UIntPtr) == 4) {
                return this.ToUInt32().ToString(format);
            }
            else {
                return this.ToUInt64().ToString(format);
            }
        }

        //| <include path='docs/doc[@for="UInt32.Parse"]/*' />
        [CLSCompliant(false)]
        public static UIntPtr Parse(String s) {
            return Parse(s, NumberStyles.Integer);
        }

        //| <include path='docs/doc[@for="UInt32.Parse3"]/*' />
        [CLSCompliant(false)]
        public unsafe static UIntPtr Parse(String s, NumberStyles style) {
            NumberFormatInfo.ValidateParseStyle(style);
            if (sizeof(UIntPtr) == 4) {
                return Number.ParseUInt32(s, style);
            }
            else {
                return Number.ParseUInt64(s, style);
            }
        }

        //| <include path='docs/doc[@for="UIntPtr.operatorUIntPtr"]/*' />
        [Intrinsic]
        [NoHeapAllocation]
        public extern static implicit operator UIntPtr (uint value);

        //| <include path='docs/doc[@for="UIntPtr.operatorUIntPtr1"]/*' />
        [Intrinsic]
        [NoHeapAllocation]
        public extern static implicit operator UIntPtr (ulong value);

#if false
        [NoHeapAllocation]
        public static implicit operator UIntPtr (int value)
        {
            return (UIntPtr)unchecked((uint)value);
        }
#endif

        [Intrinsic]
        [NoHeapAllocation]
        public extern static explicit operator IntPtr (UIntPtr value);

        //| <include path='docs/doc[@for="UIntPtr.operatoruint"]/*' />
        [Intrinsic]
        [NoHeapAllocation]
        public extern static explicit operator uint (UIntPtr value);

        //| <include path='docs/doc[@for="UIntPtr.operatorulong"]/*' />
        [Intrinsic]
        [NoHeapAllocation]
        public extern static explicit operator ulong (UIntPtr value);

        //| <include path='docs/doc[@for="UIntPtr.operatorUIntPtr2"]/*' />
        [CLSCompliant(false)]
        [Intrinsic]
        [NoHeapAllocation]
        public extern static unsafe explicit operator UIntPtr (void* value);

        //| <include path='docs/doc[@for="UIntPtr.operatorvoidMUL"]/*' />
        [CLSCompliant(false)]
        [Intrinsic]
        [NoHeapAllocation]
        public extern static unsafe explicit operator void* (UIntPtr value);

        //| <include path='docs/doc[@for="UIntPtr.operatorEQ"]/*' />
        [Intrinsic]
        [NoHeapAllocation]
        public extern static bool operator == (UIntPtr value1, UIntPtr value2);

        //| <include path='docs/doc[@for="UIntPtr.operatorNE"]/*' />
        [Intrinsic]
        [NoHeapAllocation]
        public extern static bool operator != (UIntPtr value1, UIntPtr value2);

        //| <include path='docs/doc[@for="UIntPtr.ToPointer"]/*' />
        [CLSCompliant(false)]
        [Intrinsic]
        [NoHeapAllocation]
        public extern unsafe void* ToPointer();

        [Intrinsic]
        [NoHeapAllocation]
        public extern static UIntPtr operator - (UIntPtr value1, UIntPtr value2);

        [Intrinsic]
        [NoHeapAllocation]
        public extern static UIntPtr operator - (UIntPtr value1, uint value2);

        [Intrinsic]
        [NoHeapAllocation]
        public extern static UIntPtr operator - (UIntPtr value1, int value2);

        [Intrinsic]
        [NoHeapAllocation]
        public extern static UIntPtr operator -- (UIntPtr value);

        [Intrinsic]
        [NoHeapAllocation]
        public extern static UIntPtr operator + (UIntPtr value1, UIntPtr value2);

        [Intrinsic]
        [NoHeapAllocation]
        public extern static UIntPtr operator + (UIntPtr value1, uint value2);

        [Intrinsic]
        [NoHeapAllocation]
        public extern static UIntPtr operator + (UIntPtr value1, int value2);

        [Intrinsic]
        [NoHeapAllocation]
        public extern static unsafe sbyte * operator + (sbyte *value1,
                                                        UIntPtr value2);
        [Intrinsic]
        [NoHeapAllocation]
        public extern static unsafe byte * operator + (byte *value1,
                                                     UIntPtr value2);
        [Intrinsic]
        [NoHeapAllocation]
        public extern static unsafe short * operator + (short *value1,
                                                        UIntPtr value2);

        [Intrinsic]
        [NoHeapAllocation]
        public extern static unsafe uint * operator + (uint* value1,
                                                       UIntPtr value2);
        [Intrinsic]
        [NoHeapAllocation]
        public extern static unsafe short * operator - (short *value1,
                                                        UIntPtr value2);
        [Intrinsic]
        [NoHeapAllocation]
        public extern static unsafe uint * operator - (uint* value1,
                                                       UIntPtr value2);
        [Intrinsic]
        [NoHeapAllocation]
        public extern static UIntPtr operator ++ (UIntPtr value);

        [Intrinsic]
        [NoHeapAllocation]
        public extern static UIntPtr operator * (UIntPtr value1, uint value2);

        [Intrinsic]
        [NoHeapAllocation]
        public extern static UIntPtr operator * (UIntPtr value1, UIntPtr value2);
        [Intrinsic]
        [NoHeapAllocation]
        public extern static UIntPtr operator / (UIntPtr value1, uint value2);

        [Intrinsic]
        [NoHeapAllocation]
        public extern static UIntPtr operator >> (UIntPtr value, int shift);

        [Intrinsic]
        [NoHeapAllocation]
        public extern static UIntPtr operator << (UIntPtr value, int shift);

        [Intrinsic]
        [NoHeapAllocation]
        public extern static uint operator & (UIntPtr value1, uint value2);

        [Intrinsic]
        [NoHeapAllocation]
        public extern static UIntPtr operator & (UIntPtr value1, UIntPtr value2);
        [Intrinsic]
        [NoHeapAllocation]
        public extern static UIntPtr operator | (UIntPtr value1, UIntPtr value2);
        [Intrinsic]
        [NoHeapAllocation]
        public extern static UIntPtr operator ~ (UIntPtr value);

        [Intrinsic]
        [NoHeapAllocation]
        public extern static bool operator < (UIntPtr value1, UIntPtr value2);

        [Intrinsic]
        [NoHeapAllocation]
        public extern static bool operator > (UIntPtr value1, UIntPtr value2);

        [Intrinsic]
        [NoHeapAllocation]
        public extern static bool operator <= (UIntPtr value1, UIntPtr value2);

        [Intrinsic]
        [NoHeapAllocation]
        public extern static bool operator >= (UIntPtr value1, UIntPtr value2);
    }
}
