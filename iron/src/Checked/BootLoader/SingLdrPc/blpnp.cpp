
//

//

//

//

//

//
//--


#include "bl.h"

//

//

#define PNP_STATUS_SUCCESS                  0x0000

typedef UINT16 PNP_STATUS;

//

//

#define PNP_NO_MORE_NODES                   0xFF

//

//

PPNP_INSTALLATION_CHECK BlPnpBiosInformation;
PPNP_SYSTEM_DEVICE_NODE BlPnpSystemDeviceNodeList;
UINT32 BlPnpSystemDeviceNodeListSize;
PNP_ISA_CONFIGURATION BlPnpIsaConfiguration;

//



//

UINT16 BlPnpCallFrame[16];
UINT8 BlPnpHandle;
UINT8 BlPnpNodeData[PAGE_SIZE];
UINT32 BlPnpNodeSize;
UINT8 BlPnpNumberOfNodes;

PNP_STATUS
BlPnpGetNumberOfSystemDeviceNodes(
    PUINT8 NumberOfNodes,
    PUINT32 NodeSize,
    UINT16 BiosSelector
    )


//

//

//

//

//

//

//

//

//
//--

{
    BL_LEGACY_CALL_CONTEXT Context;

    BlPnpNumberOfNodes = 0;
    BlPnpNodeSize = 0;

    BlPnpCallFrame[0] = 0;
    BlRtlConvertLinearPointerToFarPointer(&BlPnpNumberOfNodes, (PFAR_POINTER) &BlPnpCallFrame[1]);
    BlRtlConvertLinearPointerToFarPointer(&BlPnpNodeSize, (PFAR_POINTER) &BlPnpCallFrame[3]);
    BlPnpCallFrame[5] = BiosSelector;

    BlRtlZeroMemory(&Context, sizeof(BL_LEGACY_CALL_CONTEXT));

    BlRtlCallLegacyFunction(BlPnpBiosInformation->RealModeCodeSegment16,
                            BlPnpBiosInformation->RealModeCodeOffset16,
                            BlPnpCallFrame,
                            6 * sizeof(UINT16),
                            &Context,
                            &Context);

    if ((PNP_STATUS) Context.eax == PNP_STATUS_SUCCESS) {

        *NumberOfNodes = BlPnpNumberOfNodes;
        *NodeSize = BlPnpNodeSize;
    }

    return (PNP_STATUS) Context.eax;
}

PNP_STATUS
BlPnpGetSystemDeviceNode(
    PUINT8 Handle,
    PPNP_SYSTEM_DEVICE_NODE Node,
    UINT32 NodeSize,
    UINT16 Control,
    UINT16 BiosSelector
    )


//

//

//

//



//

//

//

//

//

//

//
//--

{
    BL_LEGACY_CALL_CONTEXT Context;

    BLASSERT(NodeSize > 0);

    BLASSERT(NodeSize <= sizeof(BlPnpNodeData));

    BlPnpHandle = *Handle;

    BlPnpCallFrame[0] = 1;
    BlRtlConvertLinearPointerToFarPointer(&BlPnpHandle, (PFAR_POINTER) &BlPnpCallFrame[1]);
    BlRtlConvertLinearPointerToFarPointer(BlPnpNodeData, (PFAR_POINTER) &BlPnpCallFrame[3]);
    BlPnpCallFrame[5] = Control;
    BlPnpCallFrame[6] = BiosSelector;

    BlRtlZeroMemory(&Context, sizeof(BL_LEGACY_CALL_CONTEXT));

    BlRtlCallLegacyFunction(BlPnpBiosInformation->RealModeCodeSegment16,
                            BlPnpBiosInformation->RealModeCodeOffset16,
                            BlPnpCallFrame,
                            7 * sizeof(UINT16),
                            &Context,
                            &Context);

    if ((PNP_STATUS) Context.eax == PNP_STATUS_SUCCESS) {

        *Handle = BlPnpHandle;

        BLASSERT(((PPNP_SYSTEM_DEVICE_NODE) BlPnpNodeData)->Size <= NodeSize);

        BlRtlCopyMemory(Node,
                        BlPnpNodeData,
                        ((PPNP_SYSTEM_DEVICE_NODE) BlPnpNodeData)->Size);
    }

    return (PNP_STATUS) Context.eax;
}

PNP_STATUS
BlPnpGetIsaConfiguration(
    PPNP_ISA_CONFIGURATION IsaConfiguration,
    UINT16 BiosSelector
    )


//

//

//

//

//

//

//

//
//--

{
    BL_LEGACY_CALL_CONTEXT Context;

    BlRtlZeroMemory(IsaConfiguration, sizeof(PNP_ISA_CONFIGURATION));

    IsaConfiguration->Revision = 1;

    BlPnpCallFrame[0] = 0x40;
    BlRtlConvertLinearPointerToFarPointer(IsaConfiguration, (PFAR_POINTER) &BlPnpCallFrame[1]);
    BlPnpCallFrame[3] = BiosSelector;

    BlRtlZeroMemory(&Context, sizeof(BL_LEGACY_CALL_CONTEXT));

    BlRtlCallLegacyFunction(BlPnpBiosInformation->RealModeCodeSegment16,
                            BlPnpBiosInformation->RealModeCodeOffset16,
                            BlPnpCallFrame,
                            4 * sizeof(UINT16),
                            &Context,
                            &Context);

    return (PNP_STATUS) Context.eax;
}

PPNP_INSTALLATION_CHECK
BlPnpLocateBios(
    VOID
    )


//

//

//

//


//
//--

{
    ULONG_PTR End;
    PPNP_INSTALLATION_CHECK Pnp;
    ULONG_PTR Start;

    Start = 0xF0000;
    End = 0x100000;

    while (Start != End) {

        Pnp = (PPNP_INSTALLATION_CHECK) Start;

        if ((Pnp->Signature[0] == '$') &&
            (Pnp->Signature[1] == 'P') &&
            (Pnp->Signature[2] == 'n') &&
            (Pnp->Signature[3] == 'P') &&
            (Pnp->Version == 0x10) &&
            (Pnp->Length == 0x21) &&
            (BlRtlComputeChecksum8(Pnp, Pnp->Length) == 0)
            ) {

            return Pnp;
        }

        Start += 16;
    }

    return NULL;
}

VOID
BlPnpInitialize(
    VOID
    )


//

//

//
//--

{
    UINT8 Handle;
    PPNP_SYSTEM_DEVICE_NODE Node;
    UINT32 NodeListSize;
    UINT32 NodeSize;
    UINT8 NumberOfNodes;
    PPNP_INSTALLATION_CHECK Pnp;
    PNP_STATUS Result;

    //
    
    //

    BlPnpSystemDeviceNodeList = NULL;
    BlPnpSystemDeviceNodeListSize = 0;

    //
    
    //

    Pnp = BlPnpLocateBios();

    if (Pnp == NULL) {

#if PNP_VERBOSE

        BlRtlPrintf("PNP: PNP BIOS not found!\n");

#endif

        return;
    }

#if PNP_VERBOSE

    BlRtlPrintf("PNP: PNP BIOS detected @ %p\n", Pnp);

#endif

    BlPnpBiosInformation = Pnp;

#if PNP_VERBOSE

    BlRtlPrintf("PNP:   Real-Mode Code: %04x:%04x\n",
                Pnp->RealModeCodeSegment16,
                Pnp->RealModeCodeOffset16);

    BlRtlPrintf("PNP:   Real-Mode Data: %04x:\n", Pnp->RealModeDataSegment16);

#endif

    //
    
    //

    Result = BlPnpGetNumberOfSystemDeviceNodes(&NumberOfNodes,
                                               &NodeSize,
                                               Pnp->RealModeDataSegment16);

    if (Result != PNP_STATUS_SUCCESS) {

#if PNP_VERBOSE

        BlRtlPrintf("PNP: BlPnpGetNumberOfSystemDeviceNodes failed with error %04x.\n", Result);

#endif

        return;
    }

#if PNP_VERBOSE

    BlRtlPrintf("PNP: %u node(s), %u bytes in largest node.\n",
                NumberOfNodes,
                NodeSize);

#endif

    if (NumberOfNodes == 0) {
        return;
    }

    Node = (PPNP_SYSTEM_DEVICE_NODE) BlPoolAllocateBlock(NodeSize);

    NodeListSize = 0;

    Handle = 0;

    for (;;) {

        BlRtlZeroMemory(Node, sizeof(*Node));

        Result = BlPnpGetSystemDeviceNode(&Handle,
                                          Node,
                                          NodeSize,
                                          1,
                                          Pnp->RealModeDataSegment16);

        if (Result != PNP_STATUS_SUCCESS) {

#if PNP_VERBOSE

            BlRtlPrintf("PNP: BlPnpGetSystemDeviceNode failed with error %04x.\n", Result);

#endif

            BlPoolFreeBlock(Node);

            return;
        }

        NodeListSize += Node->Size;

        if (Handle == PNP_NO_MORE_NODES) {

            break;
        }
    }

    BlPnpSystemDeviceNodeList = (PPNP_SYSTEM_DEVICE_NODE)BlPoolAllocateBlock(NodeListSize);
    BlPnpSystemDeviceNodeListSize = NodeListSize;

    Node = BlPnpSystemDeviceNodeList;

    Handle = 0;

    for (;;) {

        BlRtlZeroMemory(Node, sizeof(*Node));

        Result = BlPnpGetSystemDeviceNode(&Handle,
                                          Node,
                                          NodeSize,
                                          1,
                                          Pnp->RealModeDataSegment16);

        if (Result != PNP_STATUS_SUCCESS) {

            BlRtlPrintf("PNP: BlPnpGetSystemDeviceNode failed with error %04x.\n", Result);
            BlRtlHalt();
        }

        if (Handle == PNP_NO_MORE_NODES) {

            break;
        }

        Node = (PPNP_SYSTEM_DEVICE_NODE) (((ULONG_PTR) Node) + Node->Size);
        NodeSize -= Node->Size;
    }

#if PNP_VERBOSE

    BlRtlPrintf("PNP: DeviceNodeList: %p ... %p\n",
                BlPnpSystemDeviceNodeList,
                (ULONG_PTR) BlPnpSystemDeviceNodeList + BlPnpSystemDeviceNodeListSize - 1);

#endif

    //
    
    //

    BlPnpGetIsaConfiguration(&BlPnpIsaConfiguration, Pnp->RealModeDataSegment16);

#if PNP_VERBOSE

    BlRtlPrintf("PNP: ISA Configuration:\n"
                "PNP:   Revision                 : %u\n"
                "PNP:   # of Card Select Numbers : %u\n"
                "PNP:   Data read port           : %04x\n",
                BlPnpIsaConfiguration.Revision,
                BlPnpIsaConfiguration.NumberOfCardSelectNumbers,
                BlPnpIsaConfiguration.DataReadPort);

#endif

    return;
}
