// ----------------------------------------------------------------------------
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
// ----------------------------------------------------------------------------

//
//
//Data Encryption Standard (DES)
//------------------------------
//
//This is an implementation of the standard 56-bit DES symmetric encryption algorithm.
//DES56 is generally considered a weak algorithm, due to its short key length.
//However, it is still in use for many purposes.  I implemented it in order to implement
//the NTLM Challenge/Response authentication protocol, which uses DES to generate
//"password equivalents" from cleartext passwords.
//
//
//Implementation Notes
//--------------------
//
//This is a fairly straight-forward implementation of DES.  As such, it isn't very fast.
//I've done some work to improve performance, but performance has not been the goal,
//since the application for which I implemented it (NTLM) required only a few handful
//of DES transforms.  The priority is therefore simplicity and correctness; this isn't
//an implementation you would use for a key-space search.
//
//DES operates on 64 bit message and cipher blocks, and internally, on values that have
//several lengths: 4 bits, 6 bits, 32 bits, 48 bits, 56 bits, and 64 bits.  In many
//implementations (especially in C/C++) these values are are stored in arrays of bytes.
//I chose to store most values in 64-bit values (ulong/UInt64), partly because ulong
//is a value-type (can be stored on the stack), and partly because it makes some of the
//bit manipulation easy, and in some cases slightly parallel.
//
//I have not tested this, but my hope is that this implementation works well on 64-bit
//processors.
//
//
//Potential Performance Improvements
//----------------------------------
//
//As I said above, performance is NOT the priority of this implementation.  This code
//runs at about 1/3 the speed of another implementation that I tested against, which
//is good enough for my (current) purposes.  But we all like performance, so here are
//some ideas for improvement.
//
//  * S-box access could be improved.  The classic S-boxes are represented as 8 separate
//    arrays, each of which has 64 values, and each value of the array contains a 4-bit
//    substitution value.  This works, and is simple enough, but the data density is
//    rather low; only 4 bits of each array value are used.  So a simple improvement
//    might be to combine the 8 S-box arrays into 4 S-double-box arrays, with each
//    array containing two S-box values, one in the high nibble and one in the low.
//
//  * The permutation code could be better.  Right now, it's a loop that runs 32 or
//    48 or 64 times, and each loop iteration consists of a shift, a mask, a shift,
//    and an OR.  This could almost certainly be improved.
//
//
//References
//----------
//
//There are many references on DES.  I used:
//
//  * FIPS 46-3
//    http://csrc.nist.gov/publications/fips/fips46-3/fips46-3.pdf
//
//  * http://www.en.wikipedia.org/wiki/Data_Encryption_Standard
//
//
//
//



using System;
using System.Text;
using System.Diagnostics;

namespace System.Security.Cryptography
{
    /// <summary>
    /// This class implements the 56-bit DES algorithm.
    /// </summary>
    public sealed class Des
    {
        /// <summary>
        /// This is a "static" class in C# 2.0, but sgc doesn't support static classes.
        /// </summary>
        private Des() { }

        #region Bit Permutation Tables
        // These tables are defined in the DES specification.
        // Each table defines a permutation of a 64-bit block.
        //
        // The INDEX of each array slot is the bit (counting from the "left" or MSB)
        // of the OUTPUT, and is ZERO-based (like all sane arrays).  But the VALUE
        // of each array slot is the bit (counting from the "left" or MSB) of the
        // INPUT, and is ONE-based.  Note that the method FixPermutationTable()
        // adjusts the array value by subtracting 1.  This may seem silly, but it
        // allows us to do the subtraction at class initialization, instead of once
        // per loop iteration.
        //
        // Note that the length of each table is the number of bits that are in the
        // OUTPUT of the permutation.  The number may be less than or equal to 64.

        /// <summary>
        /// This method just runs through a shift table and converts one-based
        /// MSB-relative values to zero-based LSB-relative values (bit shift
        /// indexes).  This is a tiny, trivial improvement for ComputePermutation.
        /// </summary>
        /// <param name="shifts"></param>
        static void AdjustPermutationTable(byte[] shifts)
        {
            for (int i = 0; i < shifts.Length; i++) {
                shifts[i] = (byte)(64 - shifts[i]);
            }
        }

        /// <summary>
        /// This method performs an N-bit choice/permutation from a 64-bit input.
        /// The 'shifts' argument controls which bits are chosen for the output.
        /// </summary>
        /// <param name="input"></param>
        /// <param name="shifts"></param>
        /// <returns></returns>
        static ulong ComputePermutation(ulong input, byte[] shifts)
        {
            ulong result = 0;
            for (int i = 0; i < shifts.Length; i++) {
                result = (result << 1) | ((input >> shifts[i]) & 1);
            }

            // If the shift table contained less than 64 values, shift
            // the return value so that it is left-aligned (MSB-aligned).
            return result << (64 - shifts.Length);
        }

        /// <summary>
        /// This is the shift table for the Permuted Choice 1 (PC-1) permutation.
        /// </summary>
        static byte[] _pc1_shifts = new byte[56]
        {
              57,   49,    41,   33,    25,    17,    9,
               1,   58,    50,   42,    34,    26,   18,
              10,    2,    59,   51,    43,    35,   27,
              19,   11,     3,   60,    52,    44,   36,
              63,   55,    47,   39,    31,    23,   15,
               7,   62,    54,   46,    38,    30,   22,
              14,    6,    61,   53,    45,    37,   29,
              21,   13,     5,   28,    20,    12,    4,
        };

        /// <summary>
        /// This is the shift table for the Permuted Choice 2 (PC-2) permutation.
        /// </summary>
        static byte[] _pc2_shifts = new byte[48]
        {
             14,    17,   11,    24,     1,    5,
              3,    28,   15,     6,    21,   10,
             23,    19,   12,     4,    26,    8,
             16,     7,   27,    20,    13,    2,
             41,    52,   31,    37,    47,   55,
             30,    40,   51,    45,    33,   48,
             44,    49,   39,    56,    34,   53,
             46,    42,   50,    36,    29,   32,
        };

        /// <summary>
        /// Expansion Permutation (E).
        /// This isn't directly used any more.  Instead, we use hard-coded shifts/masks,
        /// but those shifts/masks are generated from this table.
        /// </summary>
        static readonly byte[] _expand_shifts = new byte[48]
            {
                 32,     1,    2,     3,     4,    5,
                  4,     5,    6,     7,     8,    9,
                  8,     9,   10,    11,    12,   13,
                 12,    13,   14,    15,    16,   17,
                 16,    17,   18,    19,    20,   21,
                 20,    21,   22,    23,    24,   25,
                 24,    25,   26,    27,    28,   29,
                 28,    29,   30,    31,    32,    1,
            };

        /// <summary>
        /// This is a 32-bit to 32-bit choice.  We use the usual 64-bit permutation logic for this,
        /// we just keep the value in the top 32 bits of the 64-bit ulong.
        /// </summary>
        static readonly byte[] _P_shifts = new byte[32]
            {
                16,   7,  20,  21,
                 29,  12,  28,  17,
                  1,  15,  23,  26,
                  5,  18,  31,  10,
                  2,   8,  24,  14,
                 32,  27,   3,   9,
                 19,  13,  30,   6,
                 22,  11,   4,  25,
            };

        /// <summary>
        /// Inverse Initial Permutation (IP^-1)
        /// </summary>
        static readonly byte[] _ip_inverse_shifts = new byte[64]
            {
            40,     8,   48,    16,    56,   24,    64,   32,
            39,     7,   47,    15,    55,   23,    63,   31,
            38,     6,   46,    14,    54,   22,    62,   30,
            37,     5,   45,    13,    53,   21,    61,   29,
            36,     4,   44,    12,    52,   20,    60,   28,
            35,     3,   43,    11,    51,   19,    59,   27,
            34,     2,   42,    10,    50,   18,    58,   26,
            33,     1,   41,     9,    49,   17,    57,   25,
            };

        /// <summary>
        /// Initial Permutation (IP)
        /// </summary>
        static readonly byte[] _ip_shifts = new byte[64]
            {
            58,    50,   42,    34,    26,   18,    10,    2,
            60,    52,   44,    36,    28,   20,    12,    4,
            62,    54,   46,    38,    30,   22,    14,    6,
            64,    56,   48,    40,    32,   24,    16,    8,
            57,    49,   41,    33,    25,   17,     9,    1,
            59,    51,   43,    35,    27,   19,    11,    3,
            61,    53,   45,    37,    29,   21,    13,    5,
            63,    55,   47,    39,    31,   23,    15,    7,
            };

        #endregion
        
        #region Key schedule generation

#if false
        /// <summary>
        /// This is the key rotate schedule, from the DES specification.
        /// It's used during the generation of the key table.
        /// 
        /// This is included for reference, but this implementation actually
        /// uses a slightly different means to compute the shift schedule.
        /// Instead, we store all of the bits in a single 16-bit constant,
        /// KeyRotateSchedule.
        /// </summary>
        static readonly byte[] _key_rotate_schedule =
            {
                1, 1, 2, 2, // backwards = c
                2, 2, 2, 2, // backwards = f
                1, 2, 2, 2, // backwards = e
                2, 2, 2, 1, // backwards = 7
            };
#endif

        /// <summary>
        /// This constant looks magical, but it's a very simple translation of the DES key shift schedule.
        /// The schedule is: 1, 1, 2, 2, 2, 2, 2, 2, 1, 2, 2, 2, 2, 2, 2, 1.
        /// From left to right, it is the number of bit rotates that occur on each iteration of the loop
        /// that generates keys in the key table, in the NewComputeKeyTable method.
        /// 
        /// Instead of storing the number of rotates, we just store a single bit.  If the bit is 0, then
        /// we shift once; if the bit is 1, then we shift twice.  So the schedule becomes:
        /// 
        ///     0 0 1 1 1 1 1 1 0 1 1 1 1 1 1 0
        /// 
        /// Next, rewrite this so that it is backwards, so that the MSB is on the left, which matches the
        /// usual reading order for binary/hex/decimal numbers.  Also, group them into 4-bit nybbles and
        /// convert to hexadecimal
        /// 
        ///     0 1 1 1   1 1 1 0   1 1 1 1   1 1 0 0
        ///           7         e         f         c
        /// 
        /// And you have the value of KeyRotateSchedule.  In the loop, we decide whether to shift once
        /// or twice if the "i"th bit in KeyRotateSchedule is set to 1, with i being the zero-based loop index.
        /// </summary>
        const ushort KeyRotateSchedule = 0x7efc;

        /// <summary>
        /// This method computes the key table, also known as the "key schedule".  The key table consists 
        /// of 16 pairs (C,D) of 24-bit values.  We store each pair in a single 64-bit value, with the
        /// C value MSB-aligned (occupying bits 63-40) and D immediately following (occupying bits 39-16).
        /// Bits 15-0 of each 64-bit quantity are undefined, but in practice are zero.
        /// </summary>
        /// <param name="key">The 64-bit key.  Only 56 bits are used.
        /// Bits 0, 8, 16, 24, 32, 40, 48, and 56 are ignored (LSB-relative zero-based bit indices).
        /// See the notes on PackBe and UnpackBe for information on bit order.
        /// </param>
        /// <param name="encipher">
        /// Specifies whether the keys are for enciphering or deciphering.
        /// A value of true indicates that the keys are for enciphering;
        /// the order of keys in the returned array matches the order in which they are generated.
        /// A value of false indicates that the keys are for deciphering;
        /// the order of the output array is reversed.
        /// </param>
        /// <returns>
        /// The allocated array of keys, also known as the "key schedule".
        /// </returns>
        static ulong[] ComputeKeyTable(ulong key, bool encipher)
        {
            // 'key' is a 64-bit quantity, aligned in "big endian" order.
            // The usual way to represent a DES key is an array of 8 bytes.
            // These bytes are stored in 'key' in big endian form.
            // Byte 0 occupies bits 63-48
            // Byte 1 occupies bits 47-40
            // ...
            // Byte 7 occupies bits 7-0
            // 
            // DES keys are 56 bits, not 64 bits.  So the first step is to compute the 
            // Permuted Choice 1 (PC-1) function.  This selects the 56 bits that we want,
            // and compacts them in the top 56 bits of an unsigned 64-bit integer.
            // Bits 7-0 will always be zero.
            //
            ulong keyplus = ComputePermutation(key, _pc1_shifts);
            Debug.Assert((keyplus & 0xff) == 0);

#if DES_TRACING
            Debug.WriteLine("key+:           " + ToBitStringBe(keyplus, 56, 7));
#endif
            // In DES, next we form c0 and d0.  These are two 28-bit quantities.
            // But instead of manipulating two separate 32-bit variables, we keep
            // them both (as a 56-bit quantity) in a single 64-bit variable, cd0.
            // Because our ComputePermutation deals with bits aligned to the MSB
            // of the 64-bit quantity, we don't have to do anything here.
            //
            // The variable 'cd' stores the 56-bit quantity CnDn, MSB-aligned.
            // Its initial value is K+.
            ulong cd = keyplus;

#if DES_TRACING
            Debug.WriteLine("cd0:            " + ToBitStringBe(cd, 56, 7));
#endif

            ulong[] keytable = new ulong[16];

            for (int i = 0; i < 16; i++) {
                Debug.Assert((cd & 0xff) == 0);

                // Next, we left-rotate Cn and Dn *independently* by either 1 or 2 bits.
                // By independently I mean that bit 27 of Cn becomes bit 0 of Cn, not of Dn,
                // and similarly bit 27 of Dn becomes bit 0 of Dn, not Cn.
                // The key rotate schedule tells us whether to rotate by 1 or 2 bits.
                // Because we store both C and D in a single register, we can do the
                // shifts and masks in parallel...  aren't we smart?
                bool shift2 = (KeyRotateSchedule & (1 << i)) != 0;

                if (shift2) {
                    cd = ((cd << 2) & 0xffffffcffffffc00UL)     // shift 2 sets of 27 bits left by 2
                        | ((cd >> 26) & 0x0000003000000300UL);
                }
                else {
                    // Left-rotate 2 sets of 28 bits by 1 position.
                    cd = ((cd << 1) & 0xffffffeffffffe00UL)
                        | ((cd >> 27) & 0x0000001000000100UL);
                }

                ulong k_n = ComputePermutation(cd, _pc2_shifts);
                // If we're enciphering, then store the keys sequentially.
                // For deciphering, just reverse the order of the keys.
                keytable[encipher ? i : 15 - i] = k_n;

#if false
                Debug.WriteLine(String.Format("i = {0,-2} rot={4}    c{1,-2} = {2}    d{1,-2} = {3}  k = {5}",
                    i, i + 1,
                    ToBitStringBe(cd, 28, 7),
                    ToBitStringBe(cd << 28, 28, 7),
                    shift2 ? "2" : "1",
                    ToBitStringBe(k_n, 48, 6)
                    ));
#endif

            }

            return keytable;
        }

        #endregion
        
        #region Substitution Boxes (S-boxes)

        /// <summary>
        /// This method modifies an S-box array, so that we don't need to move bits around
        /// while processing ciphers.  The DES specification, the input to each S-box
        /// lookup is a 6-bit value.  The "outer" bits (bits 5 and 0) form the row index,
        /// and the "inner" bits (bits 4-1 inclusive) form the column index.  These rows and
        /// columns have been preserved for clarity.  However, this arrangement is basically
        /// meaningless at run-time -- it's just a 6-bit table lookup.  So during class
        /// initialization, we run through all of the S-box tables and adjust rearrange
        /// the values so that we can do a direct table look-up.
        /// </summary>
        /// <param name="sbox">The S-box contents.</param>
        /// <returns>The "adjusted" S-box</returns>
        static byte[] AdjustSbox(byte[] sbox)
        {
            // In the input, bits 5 and 0 select the row, and bits 4-1 select the column.
            // Compute the index into the array.
            // (Yes, we should precompute this at some point.)
            // int i = ((input >> 1) & 0xf) | ((input << 4) & 0x10) | (input & 0x20);
            byte[] adjusted = new byte[64];

            for (int i = 0; i < 64; i++) {
                int j = ((i >> 1) & 0xf) | ((i << 4) & 0x10) | (i & 0x20);
                adjusted[i] = sbox[j];
            }

            return adjusted;
        }


        static readonly byte[] _sbox1_original = new byte[]
            {
                14,  4,  13,  1,   2, 15,  11,  8,   3, 10,   6, 12,   5,  9,   0,  7,
                0,  15,   7,  4,  14,  2,  13,  1,  10,  6,  12, 11,   9,  5,   3,  8,
                4,   1,  14,  8,  13,  6,   2, 11,  15, 12,   9,  7,   3, 10,   5,  0,
                15, 12,   8,  2,   4,  9,   1,  7,   5, 11,   3, 14,  10,  0,   6, 13,
            };


        static readonly byte[] _sbox2_original = new byte[]
        {
         15,  1,   8, 14,   6, 11,   3,  4,   9,  7,   2, 13,  12,  0,   5, 10,
          3, 13,   4,  7,  15,  2,   8, 14,  12,  0,   1, 10,   6,  9,  11,  5,
          0, 14,   7, 11,  10,  4,  13,  1,   5,  8,  12,  6,   9,  3,   2, 15,
         13,  8,  10,  1,   3, 15,   4,  2,  11,  6,   7, 12,   0,  5,  14,  9,
        };
        static readonly byte[] _sbox3_original = new byte[]
        {
             10,  0,   9, 14,   6,  3,  15,  5,   1, 13,  12,  7,  11,  4,   2,  8,
             13,  7,   0,  9,   3,  4,   6, 10,   2,  8,   5, 14,  12, 11,  15,  1,
             13,  6,   4,  9,   8, 15,   3,  0,  11,  1,   2, 12,   5, 10,  14,  7,
              1, 10,  13,  0,   6,  9,   8,  7,   4, 15,  14,  3,  11,  5,   2, 12,
        };

        static readonly byte[] _sbox4_original = new byte[]
        {

              7, 13,  14,  3,   0,  6,   9, 10,   1,  2,   8,  5,  11, 12,   4, 15,
             13,  8,  11,  5,   6, 15,   0,  3,   4,  7,   2, 12,   1, 10,  14,  9,
             10,  6,   9,  0,  12, 11,   7, 13,  15,  1,   3, 14,   5,  2,   8,  4,
              3, 15,   0,  6,  10,  1,  13,  8,   9,  4,   5, 11,  12,  7,   2, 14,
        };

        static readonly byte[] _sbox5_original = new byte[]
        {

              2, 12,   4,  1,   7, 10,  11,  6,   8,  5,   3, 15,  13,  0,  14,  9,
             14, 11,   2, 12,   4,  7,  13,  1,   5,  0,  15, 10,   3,  9,   8,  6,
              4,  2,   1, 11,  10, 13,   7,  8,  15,  9,  12,  5,   6,  3,   0, 14,
             11,  8,  12,  7,   1, 14,   2, 13,   6, 15,   0,  9,  10,  4,   5,  3,
        };

        static readonly byte[] _sbox6_original = new byte[]
        {

             12,  1,  10, 15,   9,  2,   6,  8,   0, 13,   3,  4,  14,  7,   5, 11,
             10, 15,   4,  2,   7, 12,   9,  5,   6,  1,  13, 14,   0, 11,   3,  8,
              9, 14,  15,  5,   2,  8,  12,  3,   7,  0,   4, 10,   1, 13,  11,  6,
              4,  3,   2, 12,   9,  5,  15, 10,  11, 14,   1,  7,   6,  0,   8, 13,
        };

        static readonly byte[] _sbox7_original = new byte[]
        {
              4, 11,   2, 14,  15,  0,   8, 13,   3, 12,   9,  7,   5, 10,   6,  1,
             13,  0,  11,  7,   4,  9,   1, 10,  14,  3,   5, 12,   2, 15,   8,  6,
              1,  4,  11, 13,  12,  3,   7, 14,  10, 15,   6,  8,   0,  5,   9,  2,
              6, 11,  13,  8,   1,  4,  10,  7,   9,  5,   0, 15,  14,  2,   3, 12,
        };

        static readonly byte[] _sbox8_original = new byte[]
        {
             13,  2,   8,  4,   6, 15,  11,  1,  10,  9,   3, 14,   5,  0,  12,  7,
              1, 15,  13,  8,  10,  3,   7,  4,  12,  5,   6, 11,   0, 14,   9,  2,
              7, 11,   4,  1,   9, 12,  14,  2,   0,  6,  10, 13,  15,  3,   5,  8,
              2,  1,  14,  7,   4, 10,   8, 13,  15, 12,   9,  0,   3,  5,   6, 11,
        };

        static readonly byte[] _sbox1;
        static readonly byte[] _sbox2;
        static readonly byte[] _sbox3;
        static readonly byte[] _sbox4;
        static readonly byte[] _sbox5;
        static readonly byte[] _sbox6;
        static readonly byte[] _sbox7;
        static readonly byte[] _sbox8;

        #endregion

        #region Class initialization

        static Des()
        {
            // Fix the S-box tables, so that we can use direct addressing, so we can eliminate
            // the bit shifting in GetSboxValue.
            _sbox1 = AdjustSbox(_sbox1_original);
            _sbox2 = AdjustSbox(_sbox2_original);
            _sbox3 = AdjustSbox(_sbox3_original);
            _sbox4 = AdjustSbox(_sbox4_original);
            _sbox5 = AdjustSbox(_sbox5_original);
            _sbox6 = AdjustSbox(_sbox6_original);
            _sbox7 = AdjustSbox(_sbox7_original);
            _sbox8 = AdjustSbox(_sbox8_original);

            AdjustPermutationTable(_pc1_shifts);
            AdjustPermutationTable(_pc2_shifts);
            AdjustPermutationTable(_ip_shifts);
            AdjustPermutationTable(_expand_shifts);
            AdjustPermutationTable(_ip_inverse_shifts);
            AdjustPermutationTable(_P_shifts);
        }

        #endregion

        #region DES Design time stuff
        // This section contains stuff that isn't intended to be used by the DES library
        // or its users during runtime.  It's here so that I can fiddle with performance,
        // generate code, etc.

#if DES_DESIGN_TIME_STUFF

        public static void GenExpansionCode()
        {
            byte[] shifts = _expand_shifts;

            const int result_length = 48;

            for (int kind = 0; kind < 2; kind++) {

                bool shift_then_mask = (kind == 0);
                Console.WriteLine();
                Console.WriteLine(shift_then_mask ? "SHIFT before MASK:" : "MASK before SHIFT:");
                Console.WriteLine();


                StringBuilder sb = new StringBuilder();

                // used for verifying the mask on shift-before-mask.
                ulong total_mask_sum = 0;

                // pos counts from the LEFT (MSB) to the RIGHT (MSB) of the output word.
                // the count is ZERO-based.
                int pos = 0; // index into result, counting from LEFT (MSB)
                while (pos < result_length) {

                    // destination of the shift/mask, counting from LEFT (MSB) within the destination word,
                    // and counting is ZERO based.
                    int dest = pos;


                    // source of the shift, counting from LEFT (MSB) within the source word, and counting
                    // is ONE based.
                    int src = shifts[dest];

                    // Find out how many bits we can move in a single shift/mask
                    pos++;
                    while (pos < result_length && (shifts[pos] == shifts[pos - 1] + 1))
                        pos++;
                    int run_length = pos - dest;


                    // Adjust src so that it is ZERO based, so I don't lose my mind.
                    // Note that src still counts from LEFT (MSB) to RIGHT (LSB).
                    // Now src and dest are in the same units, same direction, same offset.
                    Debug.Assert(src > 0);
                    --src;

                    // Compute a mask that will select the number of bits in the current run.
                    // Then shift it so that it will overlay the bits in the SOURCE word,
                    // since we emit the mask before the shift.
                    ulong before_mask = ((1UL << run_length) - 1) << (64 - src - run_length);
                    ulong after_mask = ((1UL << run_length) - 1) << (64 - dest - run_length);

                    if ((total_mask_sum & after_mask) != 0) {
                        Debug.WriteLine("OVERLAPPING BITS IN AFTER-MASK!");
                        Debugger.Break();
                    }
                    total_mask_sum ^= after_mask;


                    // positive means >>
                    // negative means <<
                    int right_shift = dest - src;
                    string shift_string;
                    if (right_shift > 0)
                        shift_string = String.Format(">> {0,2}", right_shift);
                    else if (right_shift < 0)
                        shift_string = String.Format("<< {0,2}", -right_shift);
                    else
                        shift_string = "";

                    if (shift_then_mask) {
                        Console.WriteLine("result |= (input {1,7}) & 0x{0:x16}UL; // src={2,2} dest={3,2} len = {4}",
                            after_mask,
                            shift_string,
                            src,
                            dest,
                            run_length);
                    }
                    else {
                        Console.WriteLine("result |= (input & 0x{0:x16}UL){1,7}; // src={2,2} dest={3,2} len = {4}",
                            before_mask,
                            shift_string,
                            src,
                            dest,
                            run_length);
                    }
                    // sb.AppendLine();
                    // 
                }

                Console.WriteLine();

                if (shift_then_mask) {
                    Console.WriteLine("total mask: 0x{0:x16}", total_mask_sum);
                    Console.WriteLine();
                }

            }

            //Console.Write(sb.ToString());
            Console.WriteLine("---");
        }

        static ulong ComputeExpansionPermutation(ulong input)
        {
            // input is 32 bits, left-aligned
            // result is 48 bits, left-aligned

#if check_expand
            ulong known_good_result = ComputePermutation(input, _expand_shifts);
#endif

#if !false
            ulong result =

              ((input << 31) & 0x8000000000000000UL) // src=31 dest= 0 len = 1
            | ((input >> 1) & 0x7c00000000000000UL) // src= 0 dest= 1 len = 5
            | ((input >> 3) & 0x03f0000000000000UL) // src= 3 dest= 6 len = 6
            | ((input >> 5) & 0x000fc00000000000UL) // src= 7 dest=12 len = 6
            | ((input >> 7) & 0x00003f0000000000UL) // src=11 dest=18 len = 6
            | ((input >> 9) & 0x000000fc00000000UL) // src=15 dest=24 len = 6
            | ((input >> 11) & 0x00000003f0000000UL) // src=19 dest=30 len = 6
            | ((input >> 13) & 0x000000000fc00000UL) // src=23 dest=36 len = 6
            | ((input >> 15) & 0x00000000003e0000UL) // src=27 dest=42 len = 5
            | ((input >> 47) & 0x0000000000010000UL) // src= 0 dest=47 len = 1
            ;

#if check_expand
            Debug.WriteLine("input:               " + ToBitStringBe(input, 32, 4));
            Debug.WriteLine("known good result:   " + ToBitStringBe(known_good_result, 48, 6));
            Debug.WriteLine("bogus result:        " + ToBitStringBe(result, 48, 6));
            Debug.WriteLine("difference:          " + ToBitStringBe(result ^ known_good_result, 48, 6, '-', 'x'));
            if (result != known_good_result) {
                Debug.WriteLine("results differ.");
                Debugger.Break();
            }
#endif
#endif

            return result;
        }
#endif // DES_DESIGN_TIME_STUFF
        #endregion

        #region Transform algorithm

        static ulong Transform(ulong[] keytable, ulong message)
        {
            // Initial Permutation
            ulong ip = ComputePermutation(message, _ip_shifts);
            // ulong ip = ComputeIP(message);

#if DES_TRACE
            if (_trace) {
                Debug.WriteLine("transform:  message: " + ToBitStringBe(message, 64, 8));
                Debug.WriteLine("            ip:      " + ToBitStringBe(ip, 64, 8));
            }
#endif

            // We keep L and R packed into a 64-bit quantity.
            // L is the top 32 bits (bits 63-32)
            // R is the bottom 32 bits (bits 31-0)
            ulong lr = ip;

            for (int i = 0; i < 16; i++) {
                // First, we compute the Expansion function of R(n-1).
                // This expands a 32 bit quantity to 48 bits.
                // This is done using a permutation table that repeats some bits in R(n-1).
                // (lr << 32) moves R(n-1) into the high bits of a 64-bit quantity (MSB alignment).
                // ulong expanded = ComputePermutation(lr << 32, _expand_shifts); // known good

                ulong r = (lr & 0xffffffffu) << 0x20;

                // These were generated by GenExpansionCode().  They are equivalent to:
                // ulong expanded = ComputePermutation(r, _expand_shifts);

                ulong expanded =
                  ((r << 31) & 0x8000000000000000UL) // src=31 dest= 0 len = 1
                | ((r >> 1) & 0x7c00000000000000UL) // src= 0 dest= 1 len = 5
                | ((r >> 3) & 0x03f0000000000000UL) // src= 3 dest= 6 len = 6
                | ((r >> 5) & 0x000fc00000000000UL) // src= 7 dest=12 len = 6
                | ((r >> 7) & 0x00003f0000000000UL) // src=11 dest=18 len = 6
                | ((r >> 9) & 0x000000fc00000000UL) // src=15 dest=24 len = 6
                | ((r >> 11) & 0x00000003f0000000UL) // src=19 dest=30 len = 6
                | ((r >> 13) & 0x000000000fc00000UL) // src=23 dest=36 len = 6
                | ((r >> 15) & 0x00000000003e0000UL) // src=27 dest=42 len = 5
                | ((r >> 47) & 0x0000000000010000UL) // src= 0 dest=47 len = 1
                ;
#if DEBUG
                ulong expanded_old_school = ComputePermutation(r, _expand_shifts);
                Debug.Assert(expanded == expanded_old_school);
#endif


                // 'expanded' now contains E(R(n-1)), but it's aligned to the top of the 64-bit register.
                // Debug.Assert((expanded & 0xffffu) == 0);

                ulong k_n = keytable[i];
                ulong b = expanded ^ k_n;

                // b is a 48-bit quantity.  We're going to collapse it down to a 32-bit quantity, using
                // the substitution boxes (S-boxes).

                ulong pre_f =
                    ((uint)_sbox1[(int)((b >> (64 - 6)) & 0x3f)] << 28) |
                    ((uint)_sbox2[(int)((b >> (64 - 12)) & 0x3f)] << 24) |
                    ((uint)_sbox3[(int)((b >> (64 - 18)) & 0x3f)] << 20) |
                    ((uint)_sbox4[(int)((b >> (64 - 24)) & 0x3f)] << 16) |
                    ((uint)_sbox5[(int)((b >> (64 - 30)) & 0x3f)] << 12) |
                    ((uint)_sbox6[(int)((b >> (64 - 36)) & 0x3f)] << 8) |
                    ((uint)_sbox7[(int)((b >> (64 - 42)) & 0x3f)] << 4) |
                    ((uint)_sbox8[(int)((b >> (64 - 48)) & 0x3f)] << 0);

                uint f = (uint)(ComputePermutation(pre_f << 32, _P_shifts) >> 32);
                // f_p appears to be correct now
                
                ulong next_l = lr & 0xffffffffu;
                ulong next_r = (lr >> 0x20);
                next_r ^= f;

                ulong next_lr = (next_l << 0x20) | next_r;

                lr = next_lr;

#if DES_TRACE
                if (_trace) {
                    Debug.WriteLine(String.Format("n={0}  e(R(n-1))={1}  e(R(n-1))+k={2} sbox={3} f={4} L({0})={5} R({0})={6}  ",
                        (i + 1).ToString().PadRight(2),
                        ToBitStringBe(expanded, 48, 6),
                        ToBitStringBe(b, 48, 6),                // expanded + k
                        ToBitStringBe((ulong)pre_f << 32, 32, 4),
                        ToBitStringBe((ulong)f << 32, 32, 4),
                        ToBitStringBe(lr, 32, 4),               // L
                        ToBitStringBe(lr << 32, 32, 4)          // R
                        ));
                }
#endif
            }

#if DES_TRACE
            if (_trace) {
                Debug.WriteLine("");
                Debug.WriteLine("LR final : " + ToBitStringBe(lr, 64, 8));
            }
#endif

            ulong rl = (lr << 0x20) | (lr >> 0x20);

            ulong result = ComputePermutation(rl, _ip_inverse_shifts);

#if DES_TRACE
            if (_trace)
                Debug.WriteLine("result: " + ToBitStringBe(result, 64, 8));
#endif
            return result;
        }

        #endregion

        #region Public encrypt / decrypt methods

        public static ulong Encrypt(ulong key, ulong message)
        {
            ulong[] keytable = ComputeKeyTable(key, true);
            return Transform(keytable, message);
        }

        public static void Encrypt(byte[] key, byte[] message, byte[] output)
        {
            ulong cipher = Encrypt(PackBe(key), PackBe(message));
            UnpackBe(cipher, output, 0);
        }

        public static void Encrypt(byte[] key, byte[] message, int message_offset, byte[] output, int output_offset)
        {
            ulong cipher = Encrypt(PackBe(key), PackBe(message, message_offset));
            UnpackBe(cipher, output, output_offset);
        }

        public static ulong Decrypt(ulong key, ulong message)
        {
            ulong[] keytable = ComputeKeyTable(key, false);
            return Transform(keytable, message);
        }

        public static void Decrypt(byte[] key, byte[] message, byte[] output)
        {
            ulong cipher = Decrypt(PackBe(key), PackBe(message));
            UnpackBe(cipher, output, 0);
        }

        public static void Decrypt(byte[] key, byte[] message, int message_offset, byte[] output, int output_offset)
        {
            ulong cipher = Decrypt(PackBe(key), PackBe(message, message_offset));
            UnpackBe(cipher, output, output_offset);
        }

        static ulong EncryptDecrypt(ulong key, ulong message, bool encipher)
        {
            ulong[] keytable = ComputeKeyTable(key, encipher);
            return Transform(keytable, message);
        }

        public static void EncryptDecrypt(byte[] key, byte[] message, byte[] result, bool encrypt)
        {
            ulong key_packed = PackBe(key);
            ulong[] keytable = ComputeKeyTable(key_packed, encrypt);
            ulong output = Transform(keytable, PackBe(message));
            UnpackBe(output, result, 0);
        }

        #endregion

        #region Bit packing

        /// <summary>
        /// Packs an array of 8 bytes into a single unsigned 64-bit integer.
        /// The packing is "big-endian"; the first byte (array[0]) is stored in bits 56-63 (inclusive)
        /// in the result, the second byte (array[1]) is stored in bits 57-48, and the last byte
        /// (array[7]) is stored in bits 7-0.
        /// </summary>
        /// <param name="array">An array of bytes to pack.</param>
        /// <returns>The packed 64-bit quantity.</returns>
        public static ulong PackBe(byte[] array)
        {
            if (array == null)
                throw new ArgumentNullException("array");
            if (array.Length < 8)
                throw new ArgumentException("The input array is too short.");

            return
                (((ulong)array[0]) << 0x38) |
                (((ulong)array[1]) << 0x30) |
                (((ulong)array[2]) << 0x28) |
                (((ulong)array[3]) << 0x20) |
                (((ulong)array[4]) << 0x18) |
                (((ulong)array[5]) << 0x10) |
                (((ulong)array[6]) << 0x08) |
                (((ulong)array[7]));
        }

        /// <summary>
        /// Packs an array of 8 bytes into a single unsigned 64-bit integer.
        /// The packing is "big-endian"; the first byte (array[offset]) is stored in bits 56-63 (inclusive)
        /// in the result, the second byte (array[offset + 1]) is stored in bits 57-48, and the last byte
        /// (array[offset + 7]) is stored in bits 7-0.
        /// </summary>
        /// <param name="array">An array of bytes to pack.</param>
        /// <param name="offset">The offset within 'array' where the bytes to read begin.</param>
        /// <returns>The packed 64-bit quantity.</returns>
        public static ulong PackBe(byte[] array, int offset)
        {
            if (array == null)
                throw new ArgumentNullException("array");
            if (offset < 0)
                throw new ArgumentOutOfRangeException("offset");
            if (array.Length < 8)
                throw new ArgumentException("The input array is too short.");

            return
                (((ulong)array[offset + 0]) << 0x38) |
                (((ulong)array[offset + 1]) << 0x30) |
                (((ulong)array[offset + 2]) << 0x28) |
                (((ulong)array[offset + 3]) << 0x20) |
                (((ulong)array[offset + 4]) << 0x18) |
                (((ulong)array[offset + 5]) << 0x10) |
                (((ulong)array[offset + 6]) << 0x08) |
                (((ulong)array[offset + 7]));
        }

        /// <summary>
        /// This method unpacks a 64-bit quantity into an array of 8 bytes.
        /// The unpacking is big-endian.
        /// See the notes on PackBe for more information.
        /// </summary>
        /// <param name="v">The value to unpack</param>
        /// <returns>An allocated array which contains the unpacked bytes.
        /// The length of this array is always 8.</returns>
        public static byte[] UnpackBe(ulong v)
        {
            byte[] array = new byte[8];
            array[0] = (byte)((v >> 0x38) & 0xff);
            array[1] = (byte)((v >> 0x30) & 0xff);
            array[2] = (byte)((v >> 0x28) & 0xff);
            array[3] = (byte)((v >> 0x20) & 0xff);
            array[4] = (byte)((v >> 0x18) & 0xff);
            array[5] = (byte)((v >> 0x10) & 0xff);
            array[6] = (byte)((v >> 0x08) & 0xff);
            array[7] = (byte)(v & 0xff);
            return array;
        }

        /// <summary>
        /// This method unpacks a 64-bit quantity into an array of 8 bytes.
        /// The unpacking is big-endian.
        /// See the notes on PackBe for more information.        /// </summary>
        /// <param name="v">The value to unpack</param>
        /// <param name="array">The array in which to store the unpacked bytes.</param>
        /// <param name="offset">The offset within 'array' of the first byte.
        /// The length of the array must be at least offset + 8.</param>
        public static void UnpackBe(ulong v, byte[] array, int offset)
        {
            array[offset + 0] = (byte)((v >> 0x38) & 0xff);
            array[offset + 1] = (byte)((v >> 0x30) & 0xff);
            array[offset + 2] = (byte)((v >> 0x28) & 0xff);
            array[offset + 3] = (byte)((v >> 0x20) & 0xff);
            array[offset + 4] = (byte)((v >> 0x18) & 0xff);
            array[offset + 5] = (byte)((v >> 0x10) & 0xff);
            array[offset + 6] = (byte)((v >> 0x08) & 0xff);
            array[offset + 7] = (byte)(v & 0xff);
        }

        #endregion

        #region Debugging

#if DES_DEBUGGING
        
#if DES_TRACE
        static bool _trace;
#endif

        static string ToHexStringBe(ulong v)
        {
            return Convert.ToString((long)v, 0x10);
        }

        static string ToBitStringBe(ulong v)
        {
            System.Text.StringBuilder buffer = new System.Text.StringBuilder();
            for (int i = 0; i < 64; i++) {
                if (i > 0 && (i % 8) == 0)
                    buffer.Append('.');

                byte b = (byte)((v >> (63 - i)) & 1);
                buffer.Append(b != 0 ? '1' : '0');
            }

            return buffer.ToString();
        }

        static string ToBitStringBe(ulong v, int length, int groupsize)
        {
            return ToBitStringBe(v, length, groupsize, '0', '1');
        }

        static string ToBitStringBe(ulong v, int length, int groupsize, char c0, char c1)
        {
            System.Text.StringBuilder buffer = new System.Text.StringBuilder();
            for (int i = 0; i < length; i++) {
                if (i > 0 && (i % groupsize) == 0)
                    buffer.Append('.');

                byte b = (byte)((v >> (63 - i)) & 1);
                buffer.Append(b != 0 ? c1 : c0);
            }

            return buffer.ToString();
        }

#endif
        #endregion
    }
}
