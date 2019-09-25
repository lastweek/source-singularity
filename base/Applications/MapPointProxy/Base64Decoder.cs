// ----------------------------------------------------------------------------
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
// ----------------------------------------------------------------------------

using System;
using Microsoft.Contracts;

internal class Base64Decoder
{
    private string fSourceStr;
    private int fCurStrIndex;
    private bool fDone;

    private int fBits;
    private int fBitsFilled;

    private const string CharsBase64  = "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/";
    private static readonly byte[] MapBase64 = ConstructMapBase64();
    private const int MaxValidChar = (int)'z';
    private const byte Invalid = unchecked((byte)-1);

    public Base64Decoder(string! sourceString, int startIndex)
    {
        fSourceStr = sourceString;
        fCurStrIndex = startIndex;
        fDone = false;
        Reset();
    }

    [Delayed]
    public void Reset()
    {
        fBits = 0;
        fBitsFilled = 0;
    }

    public byte[] Pump(int maxStrIndex, int maxReturnSize)
    {
        if ((fDone) || (fSourceStr == null)) {
            return null;
        }

        int charsConsumed;

        byte[] retval = InternalPump(fSourceStr, fCurStrIndex, maxStrIndex, maxReturnSize,
                                     out charsConsumed, out fDone);

        fCurStrIndex += charsConsumed;

        return retval;
    }

    private byte[] InternalPump(string! sourceStr, int startIndex, int maxIndex, int maxReturnSize,
                                out int charsConsumed, out bool done)
    {
        // walk hex digits pairing them up and shoving the value of each pair into a byte
        byte[] newChunk = new byte[maxReturnSize];
        int bytePos = 0;
        int charPos = startIndex;
        int b = fBits;
        int bFilled = fBitsFilled;

        while (charPos < maxIndex && bytePos < maxReturnSize) {
            char ch = sourceStr[charPos];

            // end?
            if (ch == '=') {
                done = true;
                break;
            }

            charPos++;

            // ignore white space
            if (char.IsWhiteSpace(ch)) {
                continue;
            }

            int digit;
            if (ch > 122 || (digit = MapBase64[ch]) == Invalid) {
                throw new Exception("Invalid Base64 character: " + ch);
            }

            b = ( b << 6 ) | digit;
            bFilled += 6;

            if (bFilled >= 8) {
                // get top eight valid bits
                newChunk[bytePos++] = (byte)( ( b >> ( bFilled - 8 ) ) & 0xFF );
                bFilled -= 8;

                if (bytePos == maxReturnSize) {
                    break;
                }
            }
        }

        if (bytePos < maxReturnSize) {
            if (charPos < maxIndex && sourceStr[charPos] == '=') {
                bFilled = 0;

                // ignore padding chars
                do {
                    charPos++;
                } while (charPos < maxIndex && sourceStr[charPos] == '=');

                // ignore whitespace after the padding chars
                if (charPos < maxIndex) {
                    while (charPos < maxIndex) {
                        if (!char.IsWhiteSpace(sourceStr[charPos++]))
                            throw new Exception("Invalid Base64 character: " + sourceStr[charPos - 1]);
                    }
                }
            }
        }

        fBits = b;
        fBitsFilled = bFilled;
        charsConsumed = charPos - startIndex;

        if (bytePos < maxReturnSize) {
            byte[] trimmed = new byte[bytePos];
            Buffer.BlockCopy(newChunk, 0, trimmed, 0, bytePos);
            newChunk = trimmed;

            // We ran out of characters, so we're done
            done = true;

        }
        else {
            done = false;
        }

        return newChunk;
    }

    private static byte[] ConstructMapBase64()
    {
        byte[] mapBase64 = new byte[MaxValidChar + 1];

        for (int i = 0; i < mapBase64.Length; i++) {
            mapBase64[i]= Invalid;
        }

        for (int i = 0; i < CharsBase64.Length; i++) {
            mapBase64[(int)CharsBase64[i]] = (byte)i;
        }

        return mapBase64;
    }
}
