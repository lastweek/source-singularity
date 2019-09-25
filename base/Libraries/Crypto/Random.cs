// ----------------------------------------------------------------------------
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
// ----------------------------------------------------------------------------

using System;

namespace Microsoft.Singularity.Crypto.PublicKey
{
    public class Random {
        uint[] _state;
        const int _N = 8;
        void _Mix() {
            uint[] square = new uint[_N];
            ulong carry = 0;
            for (int n = 0; n < _N; n++) {
                ulong t = carry;
                carry = 0;
                for (int i = 0; i <= n; i++) {
                    int j = n - i;
                    t += (ulong)_state[i] * _state[j];
                    carry += t >> 32;
                    t = unchecked((uint)t);
                }
                square[n] = (uint)t;
                carry += t >> 32;
            }
            square[0] |= 5;
            carry = 0;
            for (int i = 0; i < _N; i++) {
                ulong t = carry + _state[i] + square[i];
                _state[i] = unchecked((uint)t);
                carry = t >> 32;
            }
        }
        public uint Next() { _Mix(); return _state[_N - 1]; }
        public uint Next(uint n) {
            if (n <= 0) {
                throw new ArgumentException();
            }
            uint mask = 1;
            while (mask < n - 1) {
                mask = mask << 1 | 1;
            }
            while (true) {
                uint next = Next() & mask;
                if (next < n) {
                    return next;
                }
            }
        }
        public uint Next(uint lo, uint hi) {
            if (lo >= hi) {
                throw new ArgumentException();
            }
            return lo + Next(hi - lo);
        }
        public Random(uint n) {
            _state = new uint[_N];
            for (int i = 0; i < _N; i++) {
                _state[i] = n;
            }
        }
        public Random() : this(1372455507) { } // Randomly selected 32-bit integer
    }
}
