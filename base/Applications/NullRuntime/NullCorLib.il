////////////////////////////////////////////////////////////////////////////////
//
//  Microsoft Research Singularity
//
//  Copyright (c) Microsoft Corporation
//
//  The null runtime library (NullCorLib).    This is the minimal set of class
//  definitions actually needed to compile a Bartok program and produce
//  an executable that links.
//
//  All the functions in the class definitions have null bodies, so they
//  cannot run.
//
//  Note that this compilation relies on referencing meta-data provided
//  by MinCorLib, which fills in all the data layout needed for Bartok
//  to compile (for example, the layout of VTables and RuntimeTypes).

.assembly extern corlib
{
  .ver 0:0:0:0
}

.assembly NullCorLib
{
}
.module NullCorLib.dll
.imagebase 0x00400000
.subsystem 0x00000003
.file alignment 4096
.corflags 0x00000001
// Image base: 0x02c00000

//
//  TODO: add definitons or remove use of attribute classes.    Otherwise
//  they cause Bartok's meta-data reader to vector into the meta-data for
//  mincorlib, causing asserts about duplicate methods
//
// ============== CLASS STRUCTURE DECLARATION ==================

.namespace System
{

   .class public abstract auto ansi beforefieldinit Enum
        extends System.ValueType
   {
   } 

  .class public abstract auto ansi beforefieldinit ValueType
       extends System.Object
  {
   .method family hidebysig specialname rtspecialname 
         instance void  .ctor() cil managed
  {
    .maxstack  8
    ldarg.0
    call       instance void System.Object::.ctor()
    ret
  } 
  } 

  .class public auto ansi beforefieldinit Object
  {
     .custom instance void [mscorlib]System.Runtime.CompilerServices.AccessedByRuntimeAttribute::.ctor() = ( 01 00 00 00 ) 
  }

  .class public abstract sequential ansi beforefieldinit Array
  {
     .custom instance void [mscorlib]System.Runtime.CompilerServices.AccessedByRuntimeAttribute::.ctor() = ( 01 00 00 00 ) 
  } 

  .class public auto ansi beforefieldinit Exception
  {
     .custom instance void [mscorlib]System.Runtime.CompilerServices.AccessedByRuntimeAttribute::.ctor() = ( 01 00 00 00 ) 
  } // 

   .class public sequential ansi sealed beforefieldinit Byte
        extends System.ValueType
    {
    }
 
   .class public sequential ansi sealed beforefieldinit Int32
        extends System.ValueType
   {
   }

} // end of namespace System

// =============== CLASS MEMBERS DECLARATION ===================
//   note that class flags, 'extends' and 'implements' clauses
//          are provided here for information only

.namespace System
{
  .class public auto ansi beforefieldinit Exception
        extends System.Object
  {
      .field assembly string _message
      .custom instance void [corlib]System.Runtime.CompilerServices.AccessedByRuntimeAttribute::.ctor() = ( 01 00 00 00 ) 
  }

  .class public auto ansi beforefieldinit Object
  {
    .field assembly class [corlib]System.VTable vtable
    .custom instance void [corlib]System.Runtime.CompilerServices.AccessedByRuntimeAttribute::.ctor() = ( 01 00 00 00 ) 

    .method public hidebysig specialname rtspecialname 
        instance void  .ctor() cil managed
    {
	.custom instance void [corlib]System.Runtime.CompilerServices.AccessedByRuntimeAttribute::.ctor() = ( 01 00 00 00 ) 
     .maxstack  8
     ret
    } // end of method Object::.ctor


    //
    // public virtual bool Equals();
    //
    .method public hidebysig newslot virtual 
        instance bool  Equals(object obj) cil managed
    {
	.custom instance void [corlib]System.Runtime.CompilerServices.AccessedByRuntimeAttribute::.ctor() = ( 01 00 00 00 ) 
  	ldarg.0
        ldarg.1
        ceq
        ret
    }

    //
    // public virtual void Finalize()
    // 

    .method family hidebysig virtual instance void 
    Finalize() cil managed
    {
      .custom instance void [corlib]System.Runtime.CompilerServices.AccessedByRuntimeAttribute::.ctor() = ( 01 00 00 00 ) 
      .maxstack  8
      ret
    } 

    //
    // public virtual int GetHashCode()
    //
    .method public hidebysig newslot virtual 
        instance int32  GetHashCode() cil managed
    {
	.custom instance void [corlib]System.Runtime.CompilerServices.AccessedByRuntimeAttribute::.ctor() = ( 01 00 00 00 ) 
	ldc.i4.0
	ret
    }

   .method assembly hidebysig static object 
        GetObject(int32 syncBlockIndex) cil managed
    {
      .custom instance void [corlib]System.Runtime.CompilerServices.AccessedByRuntimeAttribute::.ctor() = ( 01 00 00 00 ) 
      .maxstack  1
      ldnull
      ret
    }


    //	
    // public virtual System.TypeCode GetTypeCode	
    //

    .method public hidebysig newslot virtual 
        instance valuetype [corlib]System.TypeCode 
        GetTypeCode() cil managed
    {
      .maxstack  1
      .locals (valuetype [corlib]System.TypeCode V_0)
      ldc.i4.1
      stloc.0
      ldloc.0
      ret
    }



    //
    // public virtual String ToString()
    //

    .method public hidebysig newslot virtual 
        instance string  ToString() cil managed
    {
     .maxstack  1
     .locals (string V_0)
     ldnull
     ret
    }
  }

    .class public sequential ansi sealed beforefieldinit Byte
        extends System.ValueType
    {
       .field private unsigned int8 m_value
       .custom instance void [mscorlib]System.Runtime.CompilerServices.AccessedByRuntimeAttribute::.ctor() = ( 01 00 00 00 ) 
   }

  .class public sequential ansi sealed beforefieldinit Int32
       extends  System.ValueType
  {
     .field private unsigned int32 m_value
     .custom instance void [mscorlib]System.Runtime.CompilerServices.AccessedByRuntimeAttribute::.ctor() = ( 01 00 00 00 ) 
  }

  .class public auto ansi beforefieldinit Array
	extends System.Object
  {
	.field private int32 field1
      .custom instance void [corlib]System.Runtime.CompilerServices.AccessedByRuntimeAttribute::.ctor() = ( 01 00 00 00 ) 
  }

  .class public auto ansi sealed beforefieldinit String
       extends System.Object
{
  .custom instance void [corlib]System.Runtime.CompilerServices.AccessedByRuntimeAttribute::.ctor() = ( 01 00 00 00 ) 
  .custom instance void [corlib]System.Runtime.CompilerServices.CCtorIsRunDuringStartupAttribute::.ctor() = ( 01 00 00 00 ) 

  .field private int32 m_arrayLength
  .custom instance void [corlib]System.Runtime.CompilerServices.AccessedByRuntimeAttribute::.ctor() = ( 01 00 00 00 ) 


  .field private char m_firstChar
  .custom instance void [corlib]System.Runtime.CompilerServices.AccessedByRuntimeAttribute::.ctor() = ( 01 00 00 00 ) 


.field private int32 m_stringLength
.custom instance void [corlib]System.Runtime.CompilerServices.AccessedByRuntimeAttribute::.ctor() = ( 01 00 00 00 ) 
} 
}
