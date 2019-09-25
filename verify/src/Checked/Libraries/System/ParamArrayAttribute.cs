// ==++==
//
//   Copyright (c) Microsoft Corporation.  All rights reserved.
//
// ==--==
//=============================================================================
//
// Class: ParamArrayAttribute
//
// Purpose: Container for assemblies.
//
//=============================================================================  
namespace System
{
   //| <include path='docs/doc[@for="ParamArrayAttribute"]/*' />
   [AttributeUsage (AttributeTargets.Parameter, Inherited=true, AllowMultiple=false)]
   public sealed class ParamArrayAttribute : Attribute
   {
      //| <include path='docs/doc[@for="ParamArrayAttribute.ParamArrayAttribute"]/*' />
      public ParamArrayAttribute () {}
   }
}
