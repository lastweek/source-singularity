/////////////////////////////////////////////////////////////////////////////
//
//  object.cpp - Extension to find Singularity object.
//
//  Copyright Microsoft Corporation.  All rights reserved.
//
#include "singx86.h"

#define VERBOSE 0

static bool isVtable(PSTR name,
                     __out PSTR fullclassname,
                     __out PSTR classname,
                     __out bool *vector,
                     __out bool *value)
{
    if (vector != NULL) {
        *vector = false;
    }
    if (value != NULL) {
        *value = false;
    }

    // Walk over the module name...
    while (*name && *name != '!') {
        *classname++ = *name;
        *fullclassname++ = *name++;
    }
    *classname = '\0';
    *fullclassname = '\0';

    if (*name != '!') {
        return false;
    }

    *classname++ = *name;
    *fullclassname++ = *name++;

    // Walk over the ClassVector_ if this is a vector type.
    if (strncmp(name, "ClassVector_", 12) == 0) {
        if (vector != NULL) {
            *vector = true;
        }
        name += 12;
    }

    // Walk over the Class_ or Struct_ prefix.
    if (strncmp(name, "Struct_", 7) == 0) {
        if (value != NULL) {
            *value = true;
        }
        name += 7;
    }
    else if (strncmp(name, "Class_", 6) == 0) {
        name += 6;
    }

    // Walk over the class name.
    PSTR classbeg = classname;

    while (*name && *name != ':') {
        if (*name == '_') {
            classname = classbeg;
            *fullclassname++ = *name++;
            continue;
        }
        else {
            *classname++ = *name;
            *fullclassname++ = *name++;
        }
    }
    *classname = '\0';
    *fullclassname = '\0';

    // Check if this is a vtable field.
    return ((strcmp(name, "::_vtable") == 0) ||
            (strcmp(name, "::`vftable'") == 0));
}

EXT_DECL(object) // Defines: PDEBUG_CLIENT Client, PCSTR args
{
    EXT_ENTER();    // Defines: HRESULT status = S_OK;
    UNREFERENCED_PARAMETER(args);

    ULONG64 address = 0;

    status = ExtEvalU64(&args, &address);
    if (status != S_OK) {
        goto Exit;
    }

    ULONG64 vtable = 0;
    EXT_CHECK(TraceReadPointer(1, address, &vtable));
    vtable &= ~(ULONG64)3;

    CHAR name[512];
    ULONG64 displacement = 0;
    status = g_ExtSymbols->GetNameByOffset(vtable,
                                           name,
                                           arrayof(name),
                                           NULL,
                                           &displacement);
    if (status != S_OK) {
        ExtErr("%p: No type information for vtable: [%p]\n", address, vtable);
        status = E_INVALIDARG;
        goto Exit;
    }

    if (displacement != 0) {
        ExtErr("%p: Invalid vtable %p, nearest symbol is %s+%I64d\n",
               address, vtable, name, displacement);
        status = E_INVALIDARG;
        goto Exit;
    }

    ExtVerb("%p: name %s\n", vtable, name);

    CHAR fullclassname[512];
    CHAR classname[128];
    bool vector = false;
    bool value = false;

    if (!isVtable(name, fullclassname, classname, &vector, &value)) {
        ExtErr("%p: Invalid symbol for vtable: %s\n", address, name);
        goto Exit;
    }

    ExtOut("%p: %s [vtable=%p]\n", address, classname, vtable);

    // TODO: We should automatically determine whether classname or
    // fullclassname is correct.

    CHAR command[1024];
    sprintf(command, "dt -n %s %s 0x%p", classname, args, address);
    ExtVerb("Command: %s\n", command);

    status = g_ExtControl->Execute(DEBUG_OUTCTL_ALL_CLIENTS |
                                   DEBUG_OUTCTL_OVERRIDE_MASK |
                                   DEBUG_OUTCTL_NOT_LOGGED,
                                   command,
                                   DEBUG_EXECUTE_DEFAULT );

    EXT_LEAVE();    // Macro includes: return status;
}
