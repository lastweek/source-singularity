// ==++==
//
//   Copyright (c) Microsoft Corporation.  All rights reserved.
//
// ==--==
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
//
// The Module class represents a module in the COM+ runtime.  A module
//  may consist of one or more classes and interfaces and represents a physical
//  deployment such as a DLL or EXE of those classes. There may be multiple namespaces
//  contained in a single module and a namespace may be span multiple modules.
//
// The runtime supports a special type of module that are dynamically created.  New
//  classes can be created through the dynamic IL generation process.
//
namespace System.Reflection
{
    using System;
    using System.Runtime.CompilerServices;

    //| <include path='docs/doc[@for="Module"]/*' />
    [RequiredByBartok]
    public class Module
    {
        [RequiredByBartok]
        private Assembly assembly;
        [RequiredByBartok]
        private String   scopeName;

        public Assembly Assembly 
        {
            [NoHeapAllocation]
            get { return assembly; }
        }

        public String ScopeName 
        {
            get { return scopeName; }
        }
    }
}
