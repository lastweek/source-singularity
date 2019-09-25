// ==++==
//
//   Copyright (c) Microsoft Corporation.  All rights reserved.
//
// ==--==
//=============================================================================
//
// Class: CLSCompliantAttribute
//
// Purpose: Container for assemblies.
//
//=============================================================================  

namespace System
{
    //| <include path='docs/doc[@for="CLSCompliantAttribute"]/*' />
    [AttributeUsage (AttributeTargets.All, Inherited=true, AllowMultiple=false)]
    public sealed class CLSCompliantAttribute : Attribute
    {
        private bool m_compliant;

        //| <include path='docs/doc[@for="CLSCompliantAttribute.CLSCompliantAttribute"]/*' />
        public CLSCompliantAttribute (bool isCompliant)
        {
            m_compliant = isCompliant;
        }
        //| <include path='docs/doc[@for="CLSCompliantAttribute.IsCompliant"]/*' />
        public bool IsCompliant
        {
            get
            {
                return m_compliant;
            }
        }
    }
}
