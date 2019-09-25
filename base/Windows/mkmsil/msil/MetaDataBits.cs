//
// Copyright (c) Microsoft Corporation.   All rights reserved.
//

namespace Bartok.MSIL
{

  using System;

  // MetaDataBits
  //
  // definitions for various bit-level flags, masks
  // derived from //urtdist/builds/src/2727/Lightning/Src/inc/CorHdr.h

  public enum ElementTypes: byte {
      END            = 0x0,
          VOID       = 0x1,
          BOOLEAN    = 0x2,
          CHAR       = 0x3,
          I1         = 0x4,
          U1         = 0x5,
          I2         = 0x6,
          U2         = 0x7,
          I4         = 0x8,
          U4         = 0x9,
          I8         = 0xa,
          U8         = 0xb,
          R4         = 0xc,
          R8         = 0xd,
          STRING     = 0xe,
          // every type above PTR will be simple type
          PTR        = 0xf,     // PTR <type>
          BYREF      = 0x10,    // BYREF <type>
          // Please use VALUETYPE. VALUECLASS is deprecated.
          VALUETYPE  = 0x11,    // VALUETYPE <class Token>
          CLASS      = 0x12,    // CLASS <class Token>
          VAR        = 0x13,    // a class type variable VAR <U1>
          ARRAY      = 0x14,    // MDARRAY <type> <rank> <bcount> <bound1> ... <lbcount> <lb1> ...
          GENERICINST= 0x15,    // instantiated type
          TYPEDBYREF = 0x16,    // This is a simple type.
          I          = 0x18,    // native integer size
          U          = 0x19,    // native unsigned integer size
          FNPTR      = 0x1B,    // FNPTR <complete sig for the function including calling convention>
          OBJECT     = 0x1C,    // Shortcut for System.Object
          SZARRAY    = 0x1D,    // Shortcut for single dimension zero lower bound array
                                // SZARRAY <type>
                                // This is only for binding
          MVAR       = 0x1E,    // a method type variable MVAR <U1>
          CMOD_REQD  = 0x1F,    // required C modifier : E_T_CMOD_REQD <mdTypeRef/mdTypeDef>
          CMOD_OPT   = 0x20,    // optional C modifier : E_T_CMOD_OPT <mdTypeRef/mdTypeDef>
                                // This is for signatures generated internally (which will not be persisted in any way).
          INTERNAL   = 0x21,    // INTERNAL <typehandle>
          // Note that this is the max of base type excluding modifiers
          MAX        = 0x22,    // first invalid element type
          MODIFIER   = 0x40,
          SENTINEL   = 0x01 | MODIFIER, // sentinel for varargs
          PINNED     = 0x05 | MODIFIER
  }

  public enum NativeTypes: byte {
      END         = 0x0,        //DEPRECATED
          VOID        = 0x1,    //DEPRECATED
          BOOLEAN     = 0x2,    // (4 byte boolean value: TRUE = non-zero, FALSE = 0)
          I1          = 0x3,
          U1          = 0x4,
          I2          = 0x5,
          U2          = 0x6,
          I4          = 0x7,
          U4          = 0x8,
          I8          = 0x9,
          U8          = 0xa,
          R4          = 0xb,
          R8          = 0xc,
          SYSCHAR     = 0xd,    //DEPRECATED
          VARIANT     = 0xe,    //DEPRECATED
          CURRENCY    = 0xf,
          PTR         = 0x10,   //DEPRECATED
          DECIMAL     = 0x11,   //DEPRECATED
          DATE        = 0x12,   //DEPRECATED
          BSTR        = 0x13,
          LPSTR       = 0x14,
          LPWSTR      = 0x15,
          LPTSTR      = 0x16,
          FIXEDSYSSTRING = 0x17,
          OBJECTREF   = 0x18,   //DEPRECATED
          IUNKNOWN    = 0x19,
          IDISPATCH   = 0x1a,
          STRUCT      = 0x1b,
          INTF        = 0x1c,
          SAFEARRAY   = 0x1d,
          FIXEDARRAY  = 0x1e,
          INT         = 0x1f,
          UINT        = 0x20,
          //@todo: sync up the spec
          NESTEDSTRUCT  = 0x21, //DEPRECATED (use STRUCT)
          BYVALSTR    = 0x22,
          ANSIBSTR    = 0x23,
          TBSTR       = 0x24,   // select BSTR or ANSIBSTR depending on platform
          VARIANTBOOL = 0x25,   // (2-byte boolean value: TRUE = -1, FALSE = 0)
          FUNC        = 0x26,
          ASANY       = 0x28,
          ARRAY       = 0x2a,
          LPSTRUCT    = 0x2b,
          CUSTOMMARSHALER = 0x2c, // Custom marshaler native type. This must be followed
                                // by a string of the following format:
                                // "Native type name/0Custom marshaler type name/0Optional cookie/0"
                                // Or
                                // "{Native type GUID}/0Custom marshaler type name/0Optional cookie/0"
          ERROR       = 0x2d,   // This native type coupled with ELEMENT_TYPE_I4 will map to VT_HRESULT
          MAX         = 0x50    // first invalid element type
  }

  public enum VariantTypes {
      VT_EMPTY        = 0,
          VT_NULL     = 1,
          VT_I2       = 2,
          VT_I4       = 3,
          VT_R4       = 4,
          VT_R8       = 5,
          VT_CY       = 6,
          VT_DATE     = 7,
          VT_BSTR     = 8,
          VT_DISPATCH = 9,
          VT_ERROR    = 10,
          VT_BOOL     = 11,
          VT_VARIANT  = 12,
          VT_UNKNOWN  = 13,
          VT_DECIMAL  = 14,
          VT_I1       = 16,
          VT_UI1      = 17,
          VT_UI2      = 18,
          VT_UI4      = 19,
          VT_I8       = 20,
          VT_UI8      = 21,
          VT_INT      = 22,
          VT_UINT     = 23,
          VT_VOID     = 24,
          VT_HRESULT  = 25,
          VT_PTR      = 26,
          VT_SAFEARRAY = 27,
          VT_CARRAY   = 28,
          VT_USERDEFINED = 29,
          VT_LPSTR    = 30,
          VT_LPWSTR   = 31,
          VT_RECORD   = 36,
          VT_FILETIME = 64,
          VT_BLOB     = 65,
          VT_STREAM   = 66,
          VT_STORAGE  = 67,
          VT_STREAMED_OBJECT = 68,
          VT_STORED_OBJECT = 69,
          VT_BLOB_OBJECT = 70,
          VT_CF       = 71,
          VT_CLSID    = 72,
          VT_BSTR_BLOB = 0xfff,
          VT_VECTOR   = 0x1000,
          VT_ARRAY    = 0x2000,
          VT_BYREF    = 0x4000,
          VT_RESERVED = 0x8000,
          VT_ILLEGAL  = 0xffff,
          VT_ILLEGALMASKED = 0xfff,
          VT_TYPEMASK = 0xfff
  };

  public enum SerializationTypes {
      BOOLEAN      = ElementTypes.BOOLEAN,
          CHAR         = ElementTypes.CHAR,
          I1           = ElementTypes.I1,
          U1           = ElementTypes.U1,
          I2           = ElementTypes.I2,
          U2           = ElementTypes.U2,
          I4           = ElementTypes.I4,
          U4           = ElementTypes.U4,
          I8           = ElementTypes.I8,
          U8           = ElementTypes.U8,
          R4           = ElementTypes.R4,
          R8           = ElementTypes.R8,
          STRING       = ElementTypes.STRING,
          SZARRAY      = ElementTypes.SZARRAY, // Shortcut for single dimension zero lower bound array
          TYPE         = 0x50,
          TAGGED_OBJECT= 0x51,
          FIELD        = 0x53,
          PROPERTY     = 0x54,
          ENUM         = 0x55
  };

}
