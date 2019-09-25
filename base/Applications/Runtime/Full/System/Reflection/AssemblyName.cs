// ==++==
//
//   Copyright (c) Microsoft Corporation.  All rights reserved.
//
// ==--==
//============================================================
//
// Purpose: Used for binding and retrieving info about an assembly
//
//===========================================================  
namespace System.Reflection
{
    using System.Runtime.CompilerServices;

    public partial class AssemblyName {
        public String Culture {
            get { return _Culture; }
        }

        // Set and get the name of the assembly. If this is a weak Name
        // then it optionally contains a site. For strong assembly names,
        // the name partitions up the strong name's namespace
        //| <include path='docs/doc[@for="AssemblyName.Name"]/*' />
        public String Name
        {
            get { return _Name; }
            // not needed for now
            //set { _Name = value; }
            //
        }

        //| <include path='docs/doc[@for="AssemblyName.Version"]/*' />
        public Version Version
        {
            get {
                return _Version;
            }
            // not needed for now
            //set {
            //  _Version = value;
            //}
            //
        }

        // The compressed version of the public key formed from a truncated hash.
        //| <include path='docs/doc[@for="AssemblyName.GetPublicKeyToken"]/*' />
        public byte[] GetPublicKeyToken()
        {
            // not needed for now
            //if ((_PublicKeyToken == null) &&
            //  (_Flags & AssemblyNameFlags.PublicKey) != 0)
            //      _PublicKeyToken = nGetPublicKeyToken();
            //
            return _PublicKeyToken;
        }
    }
}
