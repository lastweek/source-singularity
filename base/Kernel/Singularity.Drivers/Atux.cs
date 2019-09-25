namespace Microsoft.Singularity.Drivers
{
    public sealed class Atux
    {
        //
        // Offsets from page 146.
        //
        struct Offset
        {
            // ATU Vendor ID Register - ATUVID [p.150]
            const int ATUVID = 0x000;

            // ATU Device ID Register - ATUDID [p.150]
            const int ATUDID = 0x002;

            // ATU Command Register - ATUCMD [p.151]
            const int ATUCMD = 0x004;

            // ATU Status Register - ATUSR [p.152]
            const int ATUSR = 0x006;

            // ATU Revision ID Register - ATURID [p.154]
            const int ATURID = 0x008;

            // ATU Class Code Register - ATUCCR [p.154]
            const int ATUCCR = 0x009;

            // ATU Cacheline Size Register - ATUCLSR [p.155]
            const int ATUCLSR = 0x00C;

            // ATU Latency Timer Register - ATULT [p.155]
            const int ATULT = 0x00D;

            // ATU Header Type Register - ATUHTR [p.156]
            const int ATUHTR = 0x00E;

            // ATU BIST Register - ATUBISTR [p.157]
            const int ATUBISTR = 0x00F;

            // Inbound ATU Base Address Register 0 - IABAR0 [p.158]
            const int IABAR0 = 0x010;

            // Inbound ATU Upper Base Address Register 0 - IAUBAR0 [p.159]
            const int IAUBAR0 = 0x014;

            // Inbound ATU Base Address Register 1 - IABAR1 [p.160]
            const int IABAR1 = 0x018;

            // Inbound ATU Upper Base Address Register 1 - IAUBAR1 [p.161]
            const int IAUBAR1 = 0x01C;

            // Inbound ATU Base Address Register 2 - IABAR2 [p.162]
            const int IABAR2 = 0x020;

            // Inbound ATU Upper Base Address Register 2 - IAUBAR2 [p.163]
            const int IAUBAR2 = 0x024;

            // ATU Subsystem Vendor ID Register - ASVIR [p.164]
            const int ASVIR = 0x02C;

            // ATU Subsystem ID Register - ASIR [p.164]
            const int ASIR = 0x02E;

            // Expansion ROM Base Address Register - ERBAR [p.165]
            const int ERBAR = 0x030;

            // ATU Capabilities Pointer Register - ATU_Cap_Ptr [p.166]
            const int ATU_Cap_Ptr = 0x034;

            // ATU Interrupt Line Register - ATUILR [p.169]
            const int ATUILR = 0x03C;

            // ATU Interrupt Pin Register - ATUIPR [p.170]
            const int ATUIPR = 0x03D;

            // ATU Minimum Grant Register - ATUMGNT [p.170]
            const int ATUMGNT = 0x03E;

            // ATU Maximum Latency Register - ATUMLAT [p.171]
            const int ATUMLAT = 0x03F;

            // Inbound ATU Limit Register 0 - IALR0 [p.172]
            const int IALR0 = 0x040;

            // Inbound ATU Translate Value Register 0 - IATVR0 [p.173]
            const int IATVR0 = 0x044;

            // Inbound ATU Upper Translate Value Register 0 - IAUTVR0 [p.173]
            const int IAUTVR0 = 0x048;

            // Inbound ATU Limit Register 1 - IALR1 [p.174]
            const int IALR1 = 0x04C;

            // Inbound ATU Translate Value Register 1 - IATVR1 [p.175]
            const int IATVR1 = 0x050;

            // Inbound ATU Upper Translate Value Register 1 - IAUTVR1 [p.175]
            const int IAUTVR1 = 0x054;

            // Inbound ATU Limit Register 2 - IALR2 [p.176]
            const int IALR2 = 0x058;

            // Inbound ATU Translate Value Register 2 - IATVR2 [p.177]
            const int IATVR2 = 0x05C;

            // Inbound ATU Upper Translate Value Register 2 - IAUTVR2 [p.177]
            const int IAUTVR2 = 0x060;

            // Expansion ROM Limit Register - ERLR [p.178]
            const int ERLR = 0x064;

            // Expansion ROM Translate Value Register - ERTVR [p.179]
            const int ERTVR = 0x068;

            // Expansion ROM Upper Translate Value Register - ERUTVR [p.179]
            const int ERUTVR = 0x06C;

            // ATU Configuration Register - ATUCR [p.180]
            const int ATUCR = 0x070;

            // PCI Configuration and Status Register - PCSR [p.181]
            const int PCSR = 0x074;

            // ATU Interrupt Status Register - ATUISR [p.184]
            const int ATUISR = 0x078;

            // ATU Interrupt Mask Register - ATUIMR [p.186]
            const int ATUIMR = 0x07C;

            // VPD Capability Identifier Register - VPD_Cap_ID [p.188]
            const int VPD_Cap_ID = 0x090;

            // VPD Next Item Pointer Register - VPD_Next_Item_Ptr [p.188]
            const int VPD_Next_Item_Ptr = 0x091;

            // VPD Address Register - VPDAR [p.189]
            const int VPDAR = 0x092;

            // VPD Data Register - VPDDR [p.189]
            const int VPDDR = 0x094;

            // PM Capability Identifier Register - PM_Cap_ID [p.190]
            const int PM_Cap_ID = 0x098;

            // PM Next Item Pointer Register - PM_Next_Item_Ptr [p.190]
            const int PM_Next_Item_Ptr = 0x099;

            // ATU Power Management Capabilities Register - APMCR [p.191]
            const int APMCR = 0x09A;

            // ATU Power Management Control/Status Register - APMCSR [p.192]
            const int APMCSR = 0x09C;

            // MSI Capability Identifier Register - Cap_ID [p.452]a
            const int Cap_ID = 0x0A0;

            // MSI Next Item Pointer Register - MSI_Next_Ptr [p.453]
            const int MSI_Next_Ptr = 0x0A1;

            // Message Control Register - Message_Control [p.454]
            const int Message_Control = 0x0A2;

            // Message Address Register - Message_Address [p.455]
            const int Message_Address = 0x0A4;

            // Message Upper Address Register - Message_Upper_Address [p.456]
            const int Message_Upper_Address = 0x0A8;

            // Message Data Register - Message_Data [p.457]
            const int Message_Data = 0x0AC;

            // MSI-X Capability Identifier Register - MSI_X_Cap_ID [p.458]
            const int MSI_X_Cap_ID = 0x0B0;

            // MSI-X Next Item Pointer Register - MSI_X_Next_Item_Ptr [p.459]
            const int MSI_X_Next_Item_Ptr = 0x0B1;

            // MSI-X Message Control Register - MSI_X_MCR [p.460]
            const int MSI_X_MCR = 0x0B2;

            // MSI-X Table Offset Register - MSI_X_Table_Offset [p.461]
            const int MSI_X_Table_Offset = 0x0B4;

            // MSI-X Pending Bit Array Offset Register - MSI_X_PBA_Offset [p.462]
            const int MSI_X_PBA_Offset = 0x0B8;

            // ATU Scratch Pad Register - ATUSPR [p.193]
            const int ATUSPR = 0x0CC;

            // PCI-X Capability Identifier Register - PCI_X_Cap_ID [p.193]
            const int PCI_X_Cap_ID = 0x0D0;

            // PCI-X Next Item Pointer Register - PCI_X_Next_Item_Ptr [p.194]
            const int PCI_X_Next_Item_Ptr = 0x0D1;

            // PCI-X Command Register - PCIXCMD [p.194]
            const int PCIXCMD = 0x0D2;

            // PCI-X Status Register - PCIXSR [p.196]
            const int PCIXSR = 0x0D4;

            // ECC Control and Status Register - ECCCSR [p.198]
            const int ECCCSR = 0x0D8;

            // ECC First Address Register - ECCFAR [p.201]
            const int ECCFAR = 0x0DC;

            // ECC Second Address Register - ECCSAR [p.202]
            const int ECCSAR = 0x0E0;

            // ECC Attribute Register - ECCAR [p.203]
            const int ECCAR = 0x0E4;

            // CompactPCI Hot-Swap Capability ID Register - HS_CAPID [p.203]
            const int HS_CAPID = 0x0E8;

            // Offset EDh: Next Item Pointer - HS_NXTP [p.204]
            const int HS_NXTP = 0x0E9;

            // Hot-Swap Control/Status Register - HS_CNTRL [p.205]
            const int HS_CNTRL = 0x0EA;

            // Inbound ATU Base Address Register 3 - IABAR3 [p.207]
            const int IABAR3 = 0x200;

            // Inbound ATU Upper Base Address Register 3 - IAUBAR3 [p.208]
            const int IAUBAR3 = 0x204;

            // Inbound ATU Limit Register 3 - IALR3 [p.209]
            const int IALR3 = 0x208;

            // Inbound ATU Translate Value Register 3 - IATVR3 [p.210]
            const int IATVR3 = 0x20C;

            // Inbound ATU Upper Translate Value Register 3 - IAUTVR3 [p.210]
            const int IAUTVR3 = 0x210;

            // Outbound I/O Base Address Register - OIOBAR [p.211]
            const int OIOBAR = 0x300;

            // Outbound I/O Window Translate Value Register - OIOWTVR [p.212]
            const int OIOWTVR = 0x304;

            // Outbound Upper Memory Window Base Address Register 0 - OUMBAR0 [p.213]
            const int OUMBAR0 = 0x308;

            // Outbound Upper 32-bit Memory Window Translate Value Register 0 - OUMWTVR0 [p.214]
            const int OUMWTVR0 = 0x30C;

            // Outbound Upper Memory Window Base Address Register 1 - OUMBAR1 [p.215]
            const int OUMBAR1 = 0x310;

            // Outbound Upper 32-bit Memory Window Translate Value Register 1 - OUMWTVR1 [p.216]
            const int OUMWTVR1 = 0x314;

            // Outbound Upper Memory Window Base Address Register 2 - OUMBAR2 [p.217]
            const int OUMBAR2 = 0x318;

            // Outbound Upper 32-bit Memory Window Translate Value Register 2 - OUMWTVR2 [p.218]
            const int OUMWTVR2 = 0x31C;

            // Outbound Upper Memory Window Base Address Register 3 - OUMBAR3 [p.219]
            const int OUMBAR3 = 0x320;

            // Outbound Upper 32-bit Memory Window Translate Value Register 3 - OUMWTVR3 [p.220]
            const int OUMWTVR3 = 0x324;

            // Outbound Configuration Cycle Address Register - OCCAR [p.221]
            const int OCCAR = 0x330;

            // Outbound Configuration Cycle Data Register - OCCDR [p.222]
            const int OCCDR = 0x334;

            // Outbound Configuration Cycle Function Number - OCCFN [p.222]
            const int OCCFN = 0x338;

            // PCI Interface Error Control and Status Register - PIECSR [p.223]
            const int PIECSR = 0x380;

            // PCI Interface Error Address Register - PCIEAR [p.224]
            const int PCIEAR = 0x384;

            // PCI Interface Error Upper Address Register - PCIEUAR [p.225]
            const int PCIEUAR = 0x388;

            // PCI Interface Error Context Address Register - PCIECAR [p.226]
            const int PCIECAR = 0x38C;

            // Internal Arbiter Control Register - IACR [p.227]
            const int IACR = 0x394;

            // Multi-Transaction Timer - MTT [p.228]
            const int MTT = 0x398;

        }
    }
}
