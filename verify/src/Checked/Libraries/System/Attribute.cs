// ==++==
//
//   Copyright (c) Microsoft Corporation.  All rights reserved.
//
// ==--==
//============================================================
//
// Class:  Attribute
//
// Purpose: The class used as an attribute to denote that
//          another class can be used as an attribute.
//
//===========================================================  
namespace System
{

    using System;
    using System.Reflection;
    using System.Collections;

    //  This class is a placeholder for the compiler only!
    //  Singularity and Bartok don't support runtime access to custom attributes.

    //| <include path='docs/doc[@for="Attribute"]/*' />
    [AttributeUsageAttribute(AttributeTargets.All, Inherited = true, AllowMultiple=false)] // Base class for all attributes
    public abstract class Attribute {
        //| <include path='docs/doc[@for="Attribute.Attribute"]/*' />
        protected Attribute(){}
    }
}
