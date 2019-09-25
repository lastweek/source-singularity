/////////////////////////////////////////////////////////////////////////////
//
//  singx86.cpp - Singularity Debugger Extension.
//
//  Copyright Microsoft Corporation.  All rights reserved.
//
//  For more information, see http://ddkslingshot/webs/debugexw/
//
#include "singx86.h"
#include <strsafe.h>

ULONG   TargetMachine;
BOOL    Connected;
BOOL    UseAlternateKernelName;

PDEBUG_ADVANCED       g_ExtAdvanced;
PDEBUG_CLIENT         g_ExtClient;
PDEBUG_CONTROL4       g_ExtControl;
PDEBUG_DATA_SPACES4   g_ExtData;
PDEBUG_REGISTERS2     g_ExtRegisters;
PDEBUG_SYMBOLS        g_ExtSymbols = NULL;
PDEBUG_SYSTEM_OBJECTS g_ExtSystem;

// Queries for all debugger interfaces.
HRESULT
ExtQuery(PDEBUG_CLIENT Client)
{
    HRESULT status;

    //
    // Required interfaces.
    //

    if ((status = Client->QueryInterface(__uuidof(IDebugAdvanced),
                                         (void **)&g_ExtAdvanced)) != S_OK) {
        goto Fail;
    }
    if ((status = Client->QueryInterface(__uuidof(IDebugControl4),
                                         (void **)&g_ExtControl)) != S_OK) {
        goto Fail;
    }
    if ((status = Client->QueryInterface(__uuidof(IDebugDataSpaces4),
                                         (void **)&g_ExtData)) != S_OK) {
        goto Fail;
    }
    if ((status = Client->QueryInterface(__uuidof(IDebugRegisters2),
                                         (void **)&g_ExtRegisters)) != S_OK) {
        goto Fail;
    }
    if ((status = Client->QueryInterface(__uuidof(IDebugSymbols),
                                         (void **)&g_ExtSymbols)) != S_OK) {
        goto Fail;
    }
    if ((status = Client->QueryInterface(__uuidof(IDebugSystemObjects),
                                         (void **)&g_ExtSystem)) != S_OK) {
        goto Fail;
    }

    g_ExtClient = Client;

    return S_OK;

 Fail:
    ExtRelease();
    return status;
}

// Cleans up all debugger interfaces.
void
ExtRelease(void)
{
    g_ExtClient = NULL;
    EXT_RELEASE(g_ExtAdvanced);
    EXT_RELEASE(g_ExtControl);
    EXT_RELEASE(g_ExtData);
    EXT_RELEASE(g_ExtRegisters);
    EXT_RELEASE(g_ExtSymbols);
    EXT_RELEASE(g_ExtSystem);
}

// Normal output.
void __cdecl
ExtOut(PCSTR Format, ...)
{
    va_list Args;

    va_start(Args, Format);
    g_ExtControl->OutputVaList(DEBUG_OUTPUT_NORMAL, Format, Args);
    va_end(Args);
}

// Error output.
void __cdecl
ExtErr(PCSTR Format, ...)
{
    va_list Args;

    va_start(Args, Format);
    g_ExtControl->OutputVaList(DEBUG_OUTPUT_ERROR, Format, Args);
    va_end(Args);
}

// Warning output.
void __cdecl
ExtWarn(PCSTR Format, ...)
{
    va_list Args;

    va_start(Args, Format);
    g_ExtControl->OutputVaList(DEBUG_OUTPUT_WARNING, Format, Args);
    va_end(Args);
}

// Verbose output.
void __cdecl
ExtVerb(PCSTR Format, ...)
{
    va_list Args;

    va_start(Args, Format);
    g_ExtControl->OutputVaList(DEBUG_OUTPUT_VERBOSE, Format, Args);
    va_end(Args);
}

HRESULT
ExtEvalU64(PCSTR* Str, PULONG64 Val)
{
    HRESULT status;
    DEBUG_VALUE FullVal;
    ULONG EndIdx;

    if ((status = g_ExtControl->
         Evaluate(*Str, DEBUG_VALUE_INT64, &FullVal, &EndIdx)) != S_OK) {
        return status;
    }

    *Val = FullVal.I64;
    (*Str) += EndIdx;

    while (**Str == ' ' || **Str == '\t' ||
           **Str == '\n' || **Str == '\r') {
        (*Str)++;
    }

    return S_OK;
}

HRESULT
ExtDefPointer(ULONG64 address, PULONG64 val)
{
    *val = 0;

    return TraceReadPointer(1, address, val);
}

//////////////////////////////////////////////////////////////////////////////
//
class MyEventCallbacks : public DebugBaseEventCallbacks
{
    ULONG count;

  public:
    MyEventCallbacks()
    {
        count = 1;
    }

    STDMETHOD_(ULONG, AddRef)(THIS)
    {
        count++;
        return count;
    }

    STDMETHOD_(ULONG, Release)(THIS)
    {
        count--;
        return count;
    }

    STDMETHOD(GetInterestMask)(
        THIS_
        __out PULONG Mask)
    {
        *Mask = DEBUG_EVENT_CHANGE_DEBUGGEE_STATE;
        return S_OK;
    }

    STDMETHOD(ChangeDebuggeeState)(
        THIS_
        __in ULONG Flags,
        __in ULONG64 Argument
        )
    {
        UNREFERENCED_PARAMETER(Flags);
        UNREFERENCED_PARAMETER(Argument);

        PDEBUG_CLIENT DebugClient;
        PDEBUG_CONTROL DebugControl;
        HRESULT Hr;

        if ((Hr = DebugCreate(__uuidof(IDebugClient),
                              (void **)&DebugClient)) != S_OK) {
            return Hr;
        }

        if ((Hr = DebugClient->QueryInterface(__uuidof(IDebugControl),
                                              (void **)&DebugControl)) == S_OK) {
            return Hr;
        }

        EXT_RELEASE(DebugControl);
        EXT_RELEASE(DebugClient);

        return S_OK;
    }
};

static MyEventCallbacks g_Callback;

//////////////////////////////////////////////////////////////////////////////
//

extern "C"
HRESULT
CALLBACK
DebugExtensionInitialize(PULONG Version, PULONG Flags)
{
    PDEBUG_CLIENT DebugClient;
    PDEBUG_CONTROL DebugControl;
    HRESULT Hr;

    *Version = DEBUG_EXTENSION_VERSION(1, 0);
    *Flags = 0;
    Hr = S_OK;

    if ((Hr = DebugCreate(__uuidof(IDebugClient),
                          (void **)&DebugClient)) != S_OK) {
        return Hr;
    }

    if ((Hr = DebugClient->QueryInterface(__uuidof(IDebugControl),
                                          (void **)&DebugControl)) == S_OK) {
    }

    Hr = DebugClient->SetEventCallbacks(&g_Callback);

    ULONG execStatus = 0;
    if ((Hr = DebugControl->GetExecutionStatus(&execStatus)) == S_OK) {

        // #define DEBUG_STATUS_NO_CHANGE         0
        // #define DEBUG_STATUS_GO                1
        // #define DEBUG_STATUS_GO_HANDLED        2
        // #define DEBUG_STATUS_GO_NOT_HANDLED    3
        // #define DEBUG_STATUS_STEP_OVER         4
        // #define DEBUG_STATUS_STEP_INTO         5
        // #define DEBUG_STATUS_BREAK             6
        // #define DEBUG_STATUS_NO_DEBUGGEE       7
        // #define DEBUG_STATUS_STEP_BRANCH       8
        // #define DEBUG_STATUS_IGNORE_EVENT      9
        // #define DEBUG_STATUS_RESTART_REQUESTED 10

    }

    EXT_RELEASE(DebugControl);
    EXT_RELEASE(DebugClient);
    return Hr;
}


extern "C"
void
CALLBACK
DebugExtensionNotify(ULONG Notify, ULONG64 Argument)
{
    UNREFERENCED_PARAMETER(Argument);

    //
    // The first time we actually connect to a target
    //

    if ((Notify == DEBUG_NOTIFY_SESSION_ACCESSIBLE) && (!Connected)) {
        IDebugClient *DebugClient;
        HRESULT Hr;
        PDEBUG_CONTROL DebugControl;

        if ((Hr = DebugCreate(__uuidof(IDebugClient),
                              (void **)&DebugClient)) == S_OK) {
            //
            // Get the architecture type.
            //

            if ((Hr = DebugClient->QueryInterface(__uuidof(IDebugControl),
                                                  (void **)&DebugControl)) == S_OK) {
                if ((Hr = DebugControl->GetActualProcessorType(&TargetMachine)) == S_OK) {
                    Connected = TRUE;
                }
                OnTargetAccessible(DebugClient, DebugControl);
                DebugControl->Release();
            }
            DebugClient->Release();
        }
    }

    if (Notify == DEBUG_NOTIFY_SESSION_INACTIVE) {
        Connected = FALSE;
        TargetMachine = 0;
    }
}

//////////////////////////////////////////////////////////////////////////////

//
//Finds the kernel and initializes fields.  May fail if kernel dll isn't loaded yet.
//
HRESULT
FindKernelNameAndInitialize(PDEBUG_CLIENT client)
{
    EXT_ENTER();    // Defines: HRESULT status = S_OK;

    // Sometimes our kernel has a module name of 'kernel.*'.
    // Other times the kernel debugging infrastructure gives it a name of 'nt'.
    // Before we initialize our state, we need to know which plan we are on.
    ULONG64     module;
    ULONG       type;

    if (LEN_KERNEL_NAME < LEN_ALTERNATE_KERNEL_NAME)
    {
        ExtOut("Kernel names are updated in place, but there is insufficient space");
        return E_FAIL;
    }

    if (!UseAlternateKernelName &&
        g_ExtSymbols->GetSymbolTypeId(KERNEL_NAME "!Microsoft_Singularity_ThreadContext", &type, &module) != S_OK) {
        if (g_ExtSymbols->GetSymbolTypeId(ALTERNATE_KERNEL_NAME "!Microsoft_Singularity_ThreadContext", &type, &module) == S_OK) {
            UseAlternateKernelName = true;
            for (int i=0; i<countKernelTable; i++) {
                FixKernelName(KernelTable[i]);
            }
        }
        else {
            // We cannot find ThreadContext with either module name.  Perhaps ThreadContext is no longer a
            // valid symbol.  Do nothing.

            // TODO: FIXFIX for x64 the kernel name is nt and there are limited symbols
            // remove when BARTOK produces full debug info
            if (TargetMachine == IMAGE_FILE_MACHINE_AMD64 ) {
                UseAlternateKernelName = true;
                for (int i=0; i<countKernelTable; i++) {
                    FixKernelName(KernelTable[i]);
                }
                ExtOut("\n **** x64 system -- limited symbol support -- setting KERNEL_NAME to 'nt'\n\n");
            }
            else
            {
                // Kernel is not loaded yet.  We will load symbols lazily later.
                return S_FALSE;
            }
        }
    }

    EXT_CHECK(StructType::InitializeRegistered());

    EXT_LEAVE();    // Macro includes: return status;
}


EXT_DECL(singreload) // Defines: PDEBUG_CLIENT Client, PCSTR args
{
    EXT_ENTER();    // Defines: HRESULT status = S_OK;

    ExtOut("Reloading singularity kernel data structure descriptions...\n");

    EXT_CHECK(FindKernelNameAndInitialize(client));

    EXT_LEAVE();
}

//
//This gets called by DebugExtensionNotify when target is halted and is accessible
//
HRESULT
OnTargetAccessible(PDEBUG_CLIENT client, PDEBUG_CONTROL control)
{
    EXT_ENTER();    // Defines: HRESULT status = S_OK;

    ExtOut("**** SingX86.dll [" __DATE__ " " __TIME__ "] detected a break");
    if (Connected) {
        ExtOut(" connected to ");
        switch (TargetMachine) {
        case IMAGE_FILE_MACHINE_I386:
            ExtOut("X86");
            break;
        case IMAGE_FILE_MACHINE_IA64:
            ExtOut("IA64");
            break;
        case IMAGE_FILE_MACHINE_AMD64:
            ExtOut("x64");
            break;
        case IMAGE_FILE_MACHINE_ARM:
            ExtOut("Arm");
            break;
        default:
            ExtOut("Other[%08x]", TargetMachine);
            break;
        }
    }
    ExtOut(" ****\n");

    // Set ocommand on Win32 or Win64

    PDEBUG_SYSTEM_OBJECTS system;
    if (client->QueryInterface(__uuidof(IDebugSystemObjects),
                               (void **)&system) == S_OK) {
        char buffer[MAX_PATH];
        ULONG size;
        if (system->GetCurrentProcessExecutableName(buffer, MAX_PATH, &size) == S_OK
            && (_stricmp(buffer, "HalWin32.exe") == 0
        || _stricmp(buffer, "HalWin64.exe") == 0)) {

            EXT_CHECK(control->Execute(DEBUG_OUTCTL_IGNORE, ".ocommand HalWinDebug:",
                                       DEBUG_EXECUTE_NOT_LOGGED));
        }

        EXT_RELEASE(system);
    }

    EXT_CHECK(FindKernelNameAndInitialize(client));

    EXT_LEAVE();
}


extern "C"
void
CALLBACK
DebugExtensionUninitialize(void)
{
    PDEBUG_CLIENT DebugClient;
    HRESULT Hr;

    if ((Hr = DebugCreate(__uuidof(IDebugClient), (void **)&DebugClient)) != S_OK) {
        return;
    }

    Hr = DebugClient->SetEventCallbacks(NULL);

    EXT_RELEASE(DebugClient);
}

extern "C"
HRESULT
CALLBACK
KnownStructOutput(
    ULONG Flag,
    ULONG64 Address,
    PSTR StructName,
    PSTR Buffer,
    PULONG BufferSize
    )
{
    IDebugClient *Client;
    HRESULT status;

    if ((status = DebugCreate(__uuidof(IDebugClient),
                              (void **)&Client)) == S_OK) {
        switch (Flag) {
          case DEBUG_KNOWN_STRUCT_GET_NAMES:
            status = OnGetKnownStructNames(Client, Buffer, BufferSize);
            break;

          case DEBUG_KNOWN_STRUCT_GET_SINGLE_LINE_OUTPUT:
            status = OnGetSingleLineOutput(Client,
                                           Address,
                                           StructName,
                                           Buffer,
                                           BufferSize);
            break;

          case DEBUG_KNOWN_STRUCT_SUPPRESS_TYPE_NAME:
            status = OnGetSuppressTypeName(Client,
                                           StructName);
            break;

          default:
            status = E_INVALIDARG;
            break;
        }
    }

    EXT_RELEASE(Client);

    return status;
}

ULONG64 GetStaticPointer(PCSTR name)
{
    HRESULT status = S_OK;
    ULONG64 address;
    ULONG64 value = 0;
    EXT_CHECK(g_ExtSymbols->GetOffsetByName(name, &address));
    EXT_CHECK(TraceReadPointer(1, address, &value));
  Exit:
    return value;
}

void FixKernelName(char *candidate)
{
    // We don't enable UseAlternateKernelName without first checking (in OnTargetAccessible)
    // that KERNEL_NAME is at least as long as ALTERNATE_KERNEL_NAME.  Therefore the
    // following manipulation is just a shift down of the name in place.
    if (UseAlternateKernelName &&
        strncmp(candidate, KERNEL_NAME, LEN_KERNEL_NAME) == 0) {
        char *suffix = candidate + LEN_KERNEL_NAME;
        memcpy(candidate, ALTERNATE_KERNEL_NAME, LEN_ALTERNATE_KERNEL_NAME);
        memcpy(candidate + LEN_ALTERNATE_KERNEL_NAME, suffix, strlen(suffix) + 1);
    }
}

// Resources:

// Turn 'RES_ENTRY(g_pBootInfo, blah)' into 'char kernel_g_pBootInfo [] = { "kernel!blah" };
#define RES_ENTRY(sym, name) char kernel_ ##sym [] = { KERNEL_NAME "!" name };
#include "res.inl"
#undef RES_ENTRY

// Turn 'RES_ENTRY(g_pBootInfo, blah)' into 'kernel_g_pBootInfo,'
#define RES_ENTRY(sym, name)     kernel_ ## sym,
char *KernelTable[] = {
#include "res.inl"
};
#undef RES_ENTRY

//
///////////////////////////////////////////////////////////////// End of File.
