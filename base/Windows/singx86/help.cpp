/////////////////////////////////////////////////////////////////////////////
//
//  help.cpp - Help for Singularity Debugger Extensions.
//
//  Copyright Microsoft Corporation.  All rights reserved.
//
#include "singx86.h"

EXT_DECL(help) // Defines: PDEBUG_CLIENT Client, PCSTR args
{
    EXT_ENTER();    // Defines: HRESULT status = S_OK;
    UNREFERENCED_PARAMETER(args);

    ExtOut("Singularity Debugger Extensions:  [SingX86.dll compiled %s %s]\n"
           "  !apic                     - Dump APIC state.\n"
           "  !bytev <name>             - show byte vector information.\n"
           "  !charv <name>             - show character vector information.\n"
           //           "  !core                     - Write a core dump to disk.\n"
           "  !crashdump                - Saves minidump for further offline analysis.\n"
           "  !diag                     - Diagnosis utilities.\n"
           "  !ioapic                   - Dump I/O APIC state.\n"
           "  !log                      - Dump system log.\n"
           "  !object <address> <args>  - Display the object at address; args are same as `dt'.\n"
           "  !procs                    - List all processes.\n"
           "  !singreload               - Reloads types from kernel dll\n"
           "  !sips                     - List all SIPs.\n"
           "  !stack <address>          - Dump the stack of the given thread object.\n"
           "  !thread                   - Select the currently scheduled thread object.\n"
           "  !thread <address>         - Select the given thread object.\n"
           "  !threads                  - List all threads.\n"
           "  !threads -s               - List all threads with first 10 stack frames.\n"
           "  !threads -f               - List all threads with first 30 stack frames.\n"
           "  !threads -s -d            - List all threads with stacks more detail.\n"
           
           "  !help                     - Shows this help.\n"
           ,__DATE__, __TIME__);

    EXT_LEAVE();    // Macro includes: return status;
}
