// ----------------------------------------------------------------------------
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
// ----------------------------------------------------------------------------

using System;
using System.Diagnostics;

namespace Microsoft.Singularity.Crypto.PublicKey
{
    public class Rsa {
        public class Key {
            int _eBitN;
            byte[] _eBytes;
            Digits _eDigits;
            int _eDigitN {
                get { return (_eBitN + (Digit.BitN - 1)) / Digit.BitN; }
            }
            int _modBitN;
            byte[] _modBytes;
            int _modByteN { get { return (_modBitN + 8 - 1) / 8; } }
            Digits _modDigits;
            int _modDigitN {
                get { return (_modBitN + (Digit.BitN - 1)) / Digit.BitN; }
            }
            int[] _primeBitN;
            byte[][] _primeBytes, _dBytes;
            Modulus _modulus;
            Modulus[] _privateModulus;
            Digits[] _dDigits, _chineseDigits;
            public Key(int bitN, Random generator) {
                _modBitN = bitN;
                // The public exponent is 2^16 + 1
                _eBitN = 17;
                _eBytes = new byte[] { 1, 0, 1 };
                int p1BitN = (bitN + 1) / 2
                  , p1ByteN = (p1BitN + 7) / 8
                  , p1DigitN = (p1BitN + (Digit.BitN - 1)) / Digit.BitN
                  , p2BitN = bitN / 2
                  , p2ByteN = (p2BitN + 7) / 8
                  , p2DigitN = (p2BitN + (Digit.BitN - 1)) / Digit.BitN
                  , longerDigitN = p1DigitN > p2DigitN ? p1DigitN : p2DigitN;
                Digits d1 = new Digits(p1DigitN), d2 = new Digits(p2DigitN);
                _modDigits = new Digits(_modDigitN);
                _eDigits = new Digits(1);
                Digits gcd = new Digits(longerDigitN)
                     , temp = new Digits(longerDigitN);
                Digits.BytesToDigits(_eBytes, 0, _eDigits, _eBitN);
                int[] pBitN = new int[] { p1BitN, p2BitN };
                int nPrimeFound = 0;
                Digits p1 = null, p2 = null;
                while (nPrimeFound != 2) {
                    int pNowBitN = pBitN[nPrimeFound]
                      , pNowDigitN
                      = (pNowBitN + (Digit.BitN - 1)) / Digit.BitN;
                    Digits pNow = Prime.NewPrime(pNowBitN, generator);
                    if (nPrimeFound == 0) {
                        p1 = pNow; } else { p2 = pNow;
                    }
                    Digits.Sub(pNow, 1, temp, pNowDigitN);
                    int lgcd;
                    Digits.ExtendedGcd(_eDigits
                                     , _eDigitN
                                     , temp
                                     , pNowDigitN
                                     , nPrimeFound == 0 ? d1 : d2
                                     , null
                                     , gcd
                                     , out lgcd);
                    if (Digits.Compare(gcd, 1, lgcd) != 0) {
                        Debug.Assert(false, "untested code");
                        continue;
                    }
                    if (
                        nPrimeFound == 1
                     && Digits.Compare(p1, p1DigitN, p2, p2DigitN) == 0
                    ) {
                        Debug.Assert(false, "untested code");
                        continue;
                    }
                    nPrimeFound++;
                }
                Digits.Mul(p1, p1DigitN, p2, p2DigitN, _modDigits);
                int modBitN = Digits.SigBitN(_modDigits, _modDigitN);
                Debug.Assert(modBitN == p1BitN + p2BitN && modBitN == _modBitN
                           , "internal error");
                _primeBitN = new int[2] { p1BitN, p2BitN };
                _modBytes = new byte[_modByteN];
                _primeBytes
              = new byte[2][] { new byte[p1ByteN], new byte[p2ByteN] };
                _dBytes
              = new byte[2][] { new byte[p1ByteN], new byte[p2ByteN] };
                Digits.DigitsToBytes(_modDigits, _modBytes, 0, _modBitN);
                for (int ip = 0; ip != 2; ip++) {
                    Digits.DigitsToBytes(
                        ip == 0 ? p1 : p2, _primeBytes[ip], 0, pBitN[ip]);
                    Digits.DigitsToBytes(
                        ip == 0 ? d1 : d2, _dBytes[ip], 0, pBitN[ip]);
                }
                int moduliCreated = 0;
                Digits.BytesToDigits(_eBytes, 0, _eDigits, _eBitN);
                _modulus = new Modulus(_modDigits, _modDigitN, true);
                _privateModulus = new Modulus[2];
                _dDigits = new Digits[2];
                _chineseDigits = new Digits[2];
                for (int ip = 0; ip != 2; ip++) {
                    Digits temp2 = new Digits(_modDigitN);
                    _dDigits[ip] = new Digits(p1DigitN);
                    _chineseDigits[ip] = new Digits(p1DigitN);
                    Digits.BytesToDigits(
                        _primeBytes[ip], 0, temp2, _primeBitN[ip]);
                    _privateModulus[ip]
                  = new
                    Modulus(temp2
                          , (_primeBitN[ip] + (Digit.BitN - 1)) / Digit.BitN
                          , true);
                    moduliCreated++;
                    Digits.BytesToDigits(
                        _dBytes[ip], 0, _dDigits[ip], _primeBitN[ip]);
                }
                int lgcd2 = 0;
                Digits gcd2 = new Digits(_modDigitN);
                Digits.ExtendedGcd(_privateModulus[0]._mod
                                 , p1DigitN
                                 , _privateModulus[1]._mod
                                 , p2DigitN
                                 , _chineseDigits[1]
                                 , _chineseDigits[0]
                                 , gcd2
                                 , out lgcd2);
                if (Digits.Compare(gcd2, 1, lgcd2) != 0) {
                    throw new ArgumentException();
                }
            }
            class Block
            {
                readonly byte[] _bytes;
                readonly int _i;
                readonly int _n;
                internal Block(byte[] bytes, int i, int n) {
                    _bytes = bytes;
                    _i = i;
                    _n = n;
                }
                internal byte[] _Bytes { get { return _bytes; } }
                internal int _ByteI { get { return _i; } }
                internal int _ByteN { get { return _n; } }
                internal int _BitN { get { return 8 * _n; } }
                internal int _DigitN {
                    get { return (_BitN + (Digit.BitN - 1)) / Digit.BitN; }
                }
            }
            enum Mode { Encrypt, Decrypt };
            public byte[] _Encrypt(byte[] inputBytes, int inputByteN) {
                return _DoBlocks(inputBytes
                               , inputByteN
                               , _modByteN - 1
                               , _modByteN
                               , Mode.Encrypt);
            }
            public byte[] _Decrypt(byte[] inputBytes, int inputByteN) {
                return _DoBlocks(inputBytes
                               , inputByteN
                               , _modByteN
                               , _modByteN - 1
                               , Mode.Decrypt);
            }
            public byte[] _Sign(byte[] inputBytes, int inputByteN) {
                return _DoBlocks(inputBytes
                               , inputByteN
                               , _modByteN - 1
                               , _modByteN
                               , Mode.Decrypt);
            }
            public byte[] _Check(byte[] inputBytes, int inputByteN) {
                return _DoBlocks(inputBytes
                               , inputByteN
                               , _modByteN
                               , _modByteN - 1
                               , Mode.Encrypt);
            }
            byte[] _DoBlocks(
                byte[] inputBytes
              , int inputByteN
              , int inputBlockByteN
              , int outputBlockByteN
              , Mode mode
            ) {
                int blockN = (inputByteN + inputBlockByteN - 1)
                           / inputBlockByteN;
                byte[] outputBytes = new byte[blockN * outputBlockByteN];
                int i;
                for (i = 0; i < blockN - 1; i++) {
                    Block inputBlock
                        = new Block(
                              inputBytes, i * inputBlockByteN, inputBlockByteN)
                        , outputBlock = new Block(outputBytes
                                                , i * outputBlockByteN
                                                , outputBlockByteN);
                    if (mode == Mode.Encrypt) {
                        _EncryptBlock(inputBlock, outputBlock);
                    }
                    else {
                        _DecryptBlock(inputBlock, outputBlock);
                    }
                }
                inputByteN -= i * inputBlockByteN;
                if (inputByteN > 0) {
                    byte[] b = new byte[inputBlockByteN];
                    for (int j = 0; j < inputByteN; j++) {
                        b[j] = inputBytes[i * inputBlockByteN + j];
                    }
                    Block inputBlock = new Block(b, 0, inputBlockByteN)
                        , outputBlock = new Block(outputBytes
                                                , i * outputBlockByteN
                                                , outputBlockByteN);
                    if (mode == Mode.Encrypt) {
                        _EncryptBlock(inputBlock, outputBlock);
                    }
                    else {
                        _DecryptBlock(inputBlock, outputBlock);
                    }
                }
                return outputBytes;
            }
            void _EncryptBlock(Block input, Block output) {
                if (input == null || output == null) {
                    throw new ArgumentNullException();
                }
                Digits digits = new Digits(_modDigitN);
                Digits.BytesToDigits(
                    input._Bytes, input._ByteI, digits, input._BitN);
                Modular.ValidateData(digits, _modulus._mod, _modulus._digitN);
                _modulus._ToModular(digits, input._DigitN, digits);
                _modulus._Exp(digits, _eDigits, _eDigitN, digits);
                _modulus._FromModular(digits, digits);
                Digits.DigitsToBytes(
                    digits, output._Bytes, output._ByteI, output._BitN);
            }
            void _DecryptBlock(Block input, Block output) {
                if (input == null || output == null) {
                    throw new ArgumentNullException();
                }
                if (
                    _privateModulus[0]._digitN
                  + _privateModulus[1]._digitN
                  - _modDigitN
                  > 1
                ) {
                    throw new ArgumentException();
                }
                Digits[] dmsg = new Digits[] {
                                    new Digits(_modDigitN + 1)
                                  , new Digits(_modDigitN + 1)
                                };
                int longerDigitN
                  = _privateModulus[0]._digitN > _privateModulus[1]._digitN
                  ? _privateModulus[0]._digitN
                  : _privateModulus[1]._digitN;
                Digits res = new Digits(longerDigitN);
                Digits.BytesToDigits(
                    input._Bytes, input._ByteI, dmsg[1], input._BitN);
                Modular.ValidateData(dmsg[1], _modDigits, _modDigitN);
                for (int ip = 0; ip != 2; ip++) {
                    _privateModulus[ip]._ToModular(dmsg[1], _modDigitN, res);
                    _privateModulus[ip]
                   ._Exp(res, _dDigits[ip], _privateModulus[ip]._digitN, res);
                    _privateModulus[ip]._Mul(res, _chineseDigits[ip], res);
                    Digits.Mul(res
                             , _privateModulus[ip]._digitN
                             , _privateModulus[1 - ip]._mod
                             , _privateModulus[1 - ip]._digitN
                             , dmsg[ip]);
                }
                Modular.Add(dmsg[0], dmsg[1], dmsg[0], _modDigits, _modDigitN);
                Digits.DigitsToBytes(
                    dmsg[0], output._Bytes, output._ByteI, output._BitN);
            }
        }
    }
}
