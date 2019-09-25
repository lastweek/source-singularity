// ==++==
// 
//   Copyright (c) Microsoft Corporation.  All rights reserved.
// 
// ==--==
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
namespace System.Runtime.InteropServices
{
	using System;
    //| <include path='docs/doc[@for="CharSet"]/*' />
	public enum CharSet
    {
    	//| <include path='docs/doc[@for="CharSet.None"]/*' />
    	None = 1,		// User didn't specify how to marshal strings.
    	//| <include path='docs/doc[@for="CharSet.Ansi"]/*' />
    	Ansi = 2,		// Strings should be marshalled as ANSI 1 byte chars. 
    	//| <include path='docs/doc[@for="CharSet.Unicode"]/*' />
    	Unicode = 3,    // Strings should be marshalled as Unicode 2 byte chars.
    	//| <include path='docs/doc[@for="CharSet.Auto"]/*' />
    	Auto = 4,		// Marshal Strings in the right way for the target system. 
    }
}
