//
// Copyright (c) Microsoft Corporation.  All rights reserved.
//

// Handler for Nucleus arithmetic overflow (always fatal)
procedure Overflow();
  modifies $Eip, eax, ebx, ecx, edx, esi, edi, ebp, esp;
  ensures false;
