///////////////////////////////////////////////////////////////////////////////
//
//  Microsoft Research Singularity
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//

using System;
using System.Security.Cryptography;

interface IDes
{
    void EncryptBlock(byte[] key, byte[] input, byte[] output);
    void DecryptBlock(byte[] key, byte[] input, byte[] output);
}

class ManagedDes : IDes
{
    public void EncryptBlock(byte[] key, byte[] input, byte[] output)
    {
        Des.EncryptDecrypt(key, input, output, true);
    }

    public void DecryptBlock(byte[] key, byte[] input, byte[] output)
    {
        Des.EncryptDecrypt(key, input, output, false);
    }
}

class DesTest
{
    public static void RunTests()
    {
        IDes![]! implementations = {
            new ManagedDes(),
            // no other implementations are available on Singularity yet
        };

        TestKnownCiphers(implementations);

        TestInterop(implementations);

        foreach (IDes! des in implementations) {
            TestRandomCiphers(des);
        }

        Console.WriteLine("DES TEST: All tests complete.");
    }

    static void TestRandomCiphers(IDes! des)
    {
        Console.WriteLine("DES TEST: Testing implementation '{0}' for roundtrip encrypt/decrypt.", des.GetType().Name);
        int tickStarted = Environment.TickCount;
        int tickStopped;
        int cipherCount = 0;

        Random random = new Random();

        for (;;) {
            for (int pass = 0; pass < 0x100; pass++) {
                byte[] key = new byte[8];
                for (int i = 0; i < 8; i++)
                    key[i] = (byte)random.Next(0, 0x100);

                byte[] message = new byte[8];
                for (int i = 0; i < 8; i++)
                    message[i] = (byte)random.Next(0, 0x100);

                byte[] cipher = new byte[8];
                byte[] roundtrip_clear = new byte[8];
                des.EncryptBlock(key, message, cipher);
                cipherCount++;
                des.DecryptBlock(key, cipher, roundtrip_clear);
                cipherCount++;

                if (Util.CompareArraySpans(message, 0, roundtrip_clear, 0, 8) != 0) {
                    Console.WriteLine("DES ERROR: DES implementation '{0}' FAILED an encrypt/decrypt roundtrip test.", des.GetType().Name);
                    Console.WriteLine("    key:                " + Util.ByteArrayToStringHex(key));
                    Console.WriteLine("    clear text (input): " + Util.ByteArrayToStringHex(message));
                    Console.WriteLine("    cipher text:        " + Util.ByteArrayToStringHex(cipher));
                    Console.WriteLine("    clear text (output): " + Util.ByteArrayToStringHex(roundtrip_clear));
                    return;
                }
            }

            int now = Environment.TickCount;
            int elapsed = now - tickStarted;

            if (elapsed > 5000) {
                tickStopped = now;
                break;
            }
        }

        Console.WriteLine("    PASSED.");
        if (cipherCount > 0) {
            int totalElapsedMs = tickStopped - tickStarted;
            double ciphersPerSecond = cipherCount / ((double)totalElapsedMs) * 1000.0;
            Console.WriteLine("    Approx ciphers/sec: {0}", ciphersPerSecond);
        }
    }

    static void TestInterop(IDes![]! imps)
    {
        Console.WriteLine("TEST: Testing interoperability between different implementations.");
        Random random = new Random();
        int failureCount = 0;

        for (int pass = 0; pass < 10; pass++) {
            byte[] key = new byte[8];
            for (int i = 0; i < 8; i++)
                key[i] = (byte)random.Next(0, 0x100);

            byte[] message = new byte[8];
            for (int i = 0; i < 8; i++)
                message[i] = (byte)random.Next(0, 0x100);

            for (int i = 0; i < imps.Length; i++) {
                for (int j = 0; j < imps.Length; j++) {
                    IDes! encrypt = imps[i];
                    IDes! decrypt = imps[j];
                    byte[] cipher = new byte[message.Length];
                    byte[] clear = new byte[message.Length];
                    encrypt.EncryptBlock(key, message, cipher);
                    decrypt.DecryptBlock(key, cipher, clear);

                    int c = Util.CompareArraySpans(message, 0, clear, 0, message.Length);
                    if (c != 0) {
                        Console.WriteLine("DECRYPTED VALUES ARE DIFFERENT!");
                        Console.WriteLine("Encryptor: " + encrypt.GetType().FullName);
                        Console.WriteLine("Decryptor: " + decrypt.GetType().FullName);
                        Console.WriteLine("Clear text:");
                        Util.DumpBuffer(message);
                        Console.WriteLine("Cipher text:");
                        Util.DumpBuffer(cipher);
                        Console.WriteLine("Output text");
                        Util.DumpBuffer(clear);
                        failureCount++;

                        i = imps.Length; break;
                    }
                    else {
                        // Console.WriteLine("TEST: encrypt {0,-20} decrypt {1,-20} - ok", encrypt.GetType().Name, decrypt.GetType().Name));
                    }
                }
            }
        }

        if (failureCount == 0) {
            Console.WriteLine("    PASSED: All interoperability tests succeeded.");
        }
        else {
            Console.WriteLine("    FAILED: At least one interop test failed.");
        }
    }

    static void EmitRandomKnownCiphers()
    {
        Random random = new Random();

        Console.WriteLine("static readonly KnownCipher[] _knownCiphers = {");
        for (int i = 0; i < 0x20; i++) {
            byte[] key = new byte[8];
            random.NextBytes(key);

            byte[] message = new byte[8];
            random.NextBytes(message);

            byte[] cipher = new byte[8];
            Des.Encrypt(key, message, cipher);

            Console.WriteLine("new KnownCipher(\"{0}\", \"{1}\", \"{2}\"),",
                Util.ByteArrayToStringHex(key),
                Util.ByteArrayToStringHex(message),
                Util.ByteArrayToStringHex(cipher));
        }
        Console.WriteLine("}");
    }

    /// <summary>
    /// This method verifies that a DES implementation correctly encrypts and decrypts all of the
    /// values in the table of known ciphers.
    /// </summary>
    /// <param name="des">The implementation to test.</param>
    static void TestKnownCiphers(IDes![]! implementations)
    {
        Console.WriteLine("TEST: Testing all DES implementations against {0} known ciphers:", _knownCiphers.Length);
        foreach (IDes! des in implementations) {
            string! implementationName = (!)des.GetType().Name;

            bool passed = true;

            foreach (KnownCipher known in _knownCiphers) {
                byte[] cipher = new byte[8];
                des.EncryptBlock(known.Key, known.ClearText, cipher);

                if (Util.CompareArraySpans(cipher, 0, known.Cipher, 0, 8) != 0) {
                    Console.WriteLine("*** DES implementation '{0}' FAILED to correctly ENCIPHER a block.", implementationName);
                    Console.WriteLine("    key:                     " + Util.ByteArrayToStringHex(known.Key));
                    Console.WriteLine("    clear text:              " + Util.ByteArrayToStringHex(known.ClearText));
                    Console.WriteLine("    known good cipher text:  " + Util.ByteArrayToStringHex(known.Cipher));
                    Console.WriteLine("    failed cipher text:      " + Util.ByteArrayToStringHex(cipher));
                    passed = false;
                    break;
                }

                byte[] cleartext = new byte[8];
                des.DecryptBlock(known.Key, known.Cipher, cleartext);

                if (Util.CompareArraySpans(cipher, 0, known.Cipher, 0, 8) != 0) {
                    Console.WriteLine("*** DES implementation '{0}' FAILED to correctly DECIPHER a block.", implementationName);
                    Console.WriteLine("    key:                    " + Util.ByteArrayToStringHex(known.Key));
                    Console.WriteLine("    cipher text:            " + Util.ByteArrayToStringHex(known.ClearText));
                    Console.WriteLine("    known good clear text:  " + Util.ByteArrayToStringHex(known.Cipher));
                    Console.WriteLine("    failed clear text:      " + Util.ByteArrayToStringHex(cipher));
                    passed = false;
                    break;
                }
            }

            if (passed) {
                Console.WriteLine("    PASSED: " + implementationName);
            }
            else {
                Console.WriteLine("    FAILED: " + implementationName);
            }
        }
    }

#if false
    void TestPerformance(DesImplementation[] imps)
    {
        Console.WriteLine("TEST: Estimating performance of implementations:");

        Random random = new Random();

        foreach (DesImplementation des in imps) {
            byte[] key = new byte[0];
            random.NextBytes(key);

            byte[] cleartext = new byte[0];
        }
    }
#endif

    struct KnownCipher
    {
        public KnownCipher(string! key, string! cleartext, string! cipher)
            : this(
            Util.HexStringToByteArray(key),
            Util.HexStringToByteArray(cleartext),
            Util.HexStringToByteArray(cipher))
        {
        }

        public KnownCipher(byte[]! key, byte[]! cleartext, byte[]! cipher)
        {
            this.Key = key;
            this.ClearText = cleartext;
            this.Cipher = cipher;
        }

        public readonly byte[]! Key;
        public readonly byte[]! ClearText;
        public readonly byte[]! Cipher;
    }


    static readonly KnownCipher[] _knownCiphers =
        {
            new KnownCipher("26e9fc83852311d8", "e1402d0f9442d85c", "c0e394fd6490aa0f"),
            new KnownCipher("c95e9d039d732b6c", "2eee2417b69692a8", "bcb78b4a1215d78a"),
            new KnownCipher("7b331146c590b1d3", "6e376932bb2c030f", "555127f9a4111092"),
            new KnownCipher("e83a28ea550972b3", "be905596fff9224b", "f9656d3ec8fbab2d"),
            new KnownCipher("ae85936030929638", "adc9946509f9b101", "6b90762b582cad2d"),
            new KnownCipher("eb142f7b6da75271", "c05e88353b1ad474", "349b95d1d20d26c1"),
            new KnownCipher("141d833598a2df55", "a4f03d8b740ca9c4", "74507d68be5a8638"),
            new KnownCipher("df53abeacaa7de06", "3222a0d10961fd92", "c366707e826f47f1"),
            new KnownCipher("f52050eb757b6948", "35d9d77c6ac7fdb4", "738b39e892f934fd"),
            new KnownCipher("b5c356e76ee9aa6d", "3f7d0376020e4c42", "3b85c78032007603"),
            new KnownCipher("f3aa9654bbbd4f63", "ea63b4f0d0619c6a", "75609fcade3f50a3"),
            new KnownCipher("25ec1b450b15240b", "75e3acf777f24627", "72021f00c2d5d1ba"),
            new KnownCipher("8d9489bf31a8f8f8", "74f2fd0b35ba9cdd", "47b36b2a63ee1625"),
            new KnownCipher("e1985116f20637dd", "868aded81057ecf7", "0ef7b7b9e9253675"),
            new KnownCipher("1c8d623bd7dd397c", "f322d1181818d6bb", "5d9e33944c860522"),
            new KnownCipher("46cf16dea1303487", "5cac38a6ca1fe81d", "b665aef92e365f88"),
            new KnownCipher("0605eea757600504", "5ed422d0351fc46e", "744b0036d03d4d9b"),
            new KnownCipher("b4229141400d56ec", "59dadf2ba493b2d4", "c480de721320b5a8"),
            new KnownCipher("3ab31212292f63e5", "c9127fcc0d64523d", "d45e4fd7fbe7b1fe"),
            new KnownCipher("e7caf2a78ea6dcf8", "af024d7d81da5fcb", "37e340853ffde534"),
            new KnownCipher("224e95810cb24485", "beab772d8d89def5", "f5f9847dd156ab1b"),
            new KnownCipher("88a143daa10a4693", "d6196327e1e664ef", "e752f30bd985b91e"),
            new KnownCipher("b3b4aabfced03135", "856de9e22eaf6b26", "627247191de4454e"),
            new KnownCipher("2358f4e096852a17", "0801aaf24e1da3d7", "55da1f2d460c0d43"),
            new KnownCipher("47887ad8de1e26b7", "6f0e543321636427", "e04edfab22c74acc"),
            new KnownCipher("ae3c0389f283592d", "8a93b7cd263ee668", "50889aa8dbafb44c"),
            new KnownCipher("c9119ba635924704", "313c708731f6f6a4", "7637d6adbc64209a"),
            new KnownCipher("9c834311191ae5c3", "2f4c4e4b67599130", "6ba0e036c4584386"),
            new KnownCipher("28eb6a10c8bef21c", "f5fe57b512d1fc93", "e0a4ff1c86883af1"),
            new KnownCipher("9d1330a2fbd44fae", "2cd777e843fc9dd7", "54091b5227549171"),
            new KnownCipher("aa3f5f468ce5dcdd", "91261c1ac32fb05d", "dd5fe1a60c3fa9ed"),
            new KnownCipher("50bbae5428ef3553", "9bbbe3f04709d9f8", "ad28c355c1b48107"),
        };




}
