// ==++==
//
//   Copyright (c) Microsoft Corporation.  All rights reserved.
//
// ==--==
//=============================================================================
//
// Class: Assembly
//
// Purpose: For Assembly-related stuff.
//
//=============================================================================  

namespace System.Reflection
{

    using System;
    using System.Runtime.CompilerServices;

    //| <include path='docs/doc[@for="Assembly"]/*' />
    public partial class Assembly
    {
        // ---------- Bartok code ----------

        public AssemblyName Name
        {
            get {
                return this.assemblyName;
            }
        }

        internal String nGetSimpleName() {
            return this.assemblyName.Name;
        }

        private String GetFullName() {
            String name =
                this.nGetSimpleName()
                + ", Version=" + this.assemblyName.Version.Major
                + "." + this.assemblyName.Version.Minor
                + "." + this.assemblyName.Version.Build
                + "." + this.assemblyName.Version.Revision
                + ", Culture="
                + (this.assemblyName.Culture != ""
                   ? this.assemblyName.Culture
                   : "neutral")
                + ", PublicKeyToken="
                + (this.assemblyName.GetPublicKeyToken() != null
                   ? (Assembly.EncodeHexString
                      (this.assemblyName.GetPublicKeyToken()))
                   : "null");
            return name;
        }

        // ---------- copied from mscorlib System.Security.Util.Hex ----------

        // changed to lowercase to avoid ToLower call since the code is no
        // longer shared in Util.Hex
        private static char[] hexValues =
        { '0', '1', '2', '3', '4', '5', '6', '7', '8', '9',
          'a', 'b', 'c', 'd', 'e', 'f' };

        private static String EncodeHexString(byte[] sArray)
        {
            String result = null;

            if (sArray != null) {
                char[] hexOrder = new char[sArray.Length * 2];

                int digit;
                for (int i = 0, j = 0; i < sArray.Length; i++) {
                    digit = (int)((sArray[i] & 0xf0) >> 4);
                    hexOrder[j++] = hexValues[digit];
                    digit = (int)(sArray[i] & 0x0f);
                    hexOrder[j++] = hexValues[digit];
                }
                result = new String(hexOrder);
            }
            return result;
        }

        // ---------- mscorlib code ----------
        // (some modifications to pull in less code)

        //| <include path='docs/doc[@for="Assembly.FullName"]/*' />
        public virtual String FullName {
            get {
                // If called by Object.ToString(), return val may be NULL.
                String s;

                // not implementing InternalCache for now
                //if ((s = (String)Cache[CacheObjType.AssemblyName]) != null)
                //  return s;
                //

                s = GetFullName();
                // not implementing InternalCache for now
                //if (s != null)
                //  Cache[CacheObjType.AssemblyName] = s;
                //

                return s;
            }
        }
    }
}
