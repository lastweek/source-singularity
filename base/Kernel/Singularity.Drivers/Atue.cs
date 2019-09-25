namespace Microsoft.Singularity.Drivers
{
    public sealed class Atue
    {
        //
        // Offsets from page 299.
        //
        struct Offset
        {
            // ATU Vendor ID Register - ATUVID [p.303]
            const int ATUVID = 0x000;

            // ATU Device ID Register - ATUDID [p.303]
            const int ATUDID = 0x002;

            // ATU Command Register - ATUCMD [p.304]
            const int ATUCMD = 0x004;

            // ATU Status Register - ATUSR [p.305]
            const int ATUSR = 0x006;

            // ATU Revision ID Register - ATURID [p.306]
            const int ATURID = 0x008;

            // ATU Class Code Register - ATUCCR [p.306]
            const int ATUCCR = 0x009;

            // ATU Cacheline Size Register - ATUCLSR [p.307]
            const int ATUCLSR = 0x00C;

            // ATU Latency Timer Register - ATULT [p.307]
            const int ATULT = 0x00D;

            // ATU Header Type Register - ATUHTR [p.308]
            const int ATUHTR = 0x00E;

            // ATU BIST Register - ATUBISTR [p.309]
            const int ATUBISTR = 0x00F;

            // Inbound ATU Base Address Register 0 - IABAR0 [p.310]
            const int IABAR0 = 0x010;

            // Inbound ATU Upper Base Address Register 0 - IAUBAR0 [p.311]
            const int IAUBAR0 = 0x014;

            // Inbound ATU Base Address Register 1 - IABAR1 [p.314]
            const int IABAR1 = 0x018;

            // Inbound ATU Upper Base Address Register 1 - IAUBAR1 [p.315]
            const int IAUBAR1 = 0x01C;

            // Inbound ATU Base Address Register 2 - IABAR2 [p.316]
            const int IABAR2 = 0x020;

            // Inbound ATU Upper Base Address Register 2 - IAUBAR2 [p.317]
            const int IAUBAR2 = 0x024;

            // ATU Subsystem Vendor ID Register - ASVIR [p.318]
            const int ASVIR = 0x02C;

            // ATU Subsystem ID Register - ASIR [p.318]
            const int ASIR = 0x02E;

            // Expansion ROM Base Address Register - ERBAR [p.319]
            const int ERBAR = 0x030;

            // ATU Capabilities Pointer Register - ATU_Cap_Ptr [p.320]
            const int ATU_Cap_Ptr = 0x034;

            // ATU Interrupt Line Register - ATUILR [p.321]
            const int ATUILR = 0x03C;

            // ATU Interrupt Pin Register - ATUIPR [p.322]
            const int ATUIPR = 0x03D;

            // ATU Minimum Grant Register - ATUMGNT [p.322]
            const int ATUMGNT = 0x03E;

            // ATU Maximum Latency Register - ATUMLAT [p.323]
            const int ATUMLAT = 0x03F;

            // Inbound ATU Limit Register 0 - IALR0 [p.324]
            const int IALR0 = 0x040;

            // Inbound ATU Translate Value Register 0 - IATVR0 [p.325]
            const int IATVR0 = 0x044;

            // Inbound ATU Upper Translate Value Register 0 - IAUTVR0 [p.325]
            const int IAUTVR0 = 0x048;

            // Inbound ATU Limit Register 1 - IALR1 [p.326]
            const int IALR1 = 0x04C;

            // Inbound ATU Translate Value Register 1 - IATVR1 [p.327]
            const int IATVR1 = 0x050;

            // Inbound ATU Upper Translate Value Register 1 - IAUTVR1 [p.327]
            const int IAUTVR1 = 0x054;

            // Inbound ATU Limit Register 2 - IALR2 [p.328]
            const int IALR2 = 0x058;

            // Inbound ATU Translate Value Register 2 - IATVR2 [p.329]
            const int IATVR2 = 0x05C;

            // Inbound ATU Upper Translate Value Register 2 - IAUTVR2 [p.330]
            const int IAUTVR2 = 0x060;

            // Expansion ROM Limit Register - ERLR [p.330]
            const int ERLR = 0x064;

            // Expansion ROM Translate Value Register - ERTVR [p.331]
            const int ERTVR = 0x068;

            // Expansion ROM Upper Translate Value Register - ERUTVR [p.331]
            const int ERUTVR = 0x06C;

            // ATU Configuration Register - ATUCR [p.332]
            const int ATUCR = 0x070;

            // PCI Configuration and Status Register - PCSR [p.333]
            const int PCSR = 0x074;

            // ATU Interrupt Status Register - ATUISR [p.335]
            const int ATUISR = 0x078;

            // ATU Interrupt Mask Register - ATUIMR [p.338]
            const int ATUIMR = 0x07C;

            // PCI Express Message Control/Status Register - PEMCSR [p.339]
            const int PEMCSR = 0x080;

            // PCI Express Link Control/Status Register - PELCSR [p.340]
            const int PELCSR = 0x084;

            // VPD Capability Identifier Register - VPD_Cap_ID [p.341]
            const int VPD_Cap_ID = 0x090;

            // VPD Next Item Pointer Register - VPD_Next_Item_Ptr [p.341]
            const int VPD_Next_Item_Ptr = 0x091;

            // VPD Address Register - VPDAR [p.342]
            const int VPDAR = 0x092;

            // VPD Data Register - VPDDR [p.342]
            const int VPDDR = 0x094;

            // PM Capability Identifier Register - PM_Cap_ID [p.343]
            const int PM_Cap_ID = 0x098;

            // PM Next Item Pointer Register - PM_Next_Item_Ptr [p.343]
            const int PM_Next_Item_Ptr = 0x099;

            // ATU Power Management Capabilities Register - APMCR [p.344]
            const int APMCR = 0x09A;

            // ATU Power Management Control/Status Register - APMCSR [p.345]
            const int APMCSR = 0x09C;

            // MSI Capability Identifier Register - Cap_ID [p.452a]
            const int Cap_ID = 0x0A0;

            // MSI Next Item Pointer Register - MSI_Next_Ptr [p.453a]
            const int MSI_Next_Ptr = 0x0A1;

            // Message Control Register - Message_Control [p.454a]
            const int Message_Control = 0x0A2;

            // Message Address Register - Message_Address [p.455a]
            const int Message_Address = 0x0A4;

            // Message Upper Address Register - Message_Upper_Address [p.456a]
            const int Message_Upper_Address = 0x0A8;

            // Message Data Register- Message_Data [p.457a]
            const int Message_Data = 0x0AC;

            // MSI-X Capability Identifier Register - MSI_X_Cap_ID [p.458b]
            const int MSI_X_Cap_ID = 0x0B0;

            // MSI-X Next Item Pointer Register - MSI_X_Next_Item_Ptr [p.459b]
            const int MSI_X_Next_Item_Ptr = 0x0B1;

            // MSI-X Message Control Register - MSI_X_MCR [p.460b]
            const int MSI_X_MCR = 0x0B2;

            // MSI-X Table Offset Register — MSI_X_Table_Offset [p.461b]
            const int MSX_X_Table_Offset = 0x0B4;

            // MSI-X Pending Bit Array Offset Register - MSI_X_PBA_Offset [p.462b]
            const int MSI_X_PBA_Offset = 0x0B8;

            // ATU Scratch Pad Register - ATUSPR [p.346]
            const int ATUSPR = 0x0CC;

            // PCI Express Capability List Register - PCIE_CAPID [p.346]
            const int PCIE_CAPID = 0x0D0;

            // PCI Express Next Item Pointer Register - PCIE_NXTP [p.347]
            const int PCIE_NXTP = 0x0D1;

            // PCI Express Capabilities Register - PCIE_CAP [p.348]
            const int PCIE_CAP = 0x0D2;

            // PCI Express Device Capabilities Register - PCIE_DCAP [p.349]
            const int PCIE_DCAP = 0x0D4;

            // PCI Express Device Control Register - PE_DCTL [p.350]
            const int PE_DCTL = 0x0D8;

            // PCI Express Device Status Register - PE_DSTS [p.352]
            const int PE_DSTS = 0x0DA;

            // PCI Express Link Capabilities Register - PE_LCAP [p.353]
            const int PE_LCAP = 0x0DC;

            // PCI Express Link Control Register - PE_LCTL [p.354]
            const int PE_LCTL = 0x0E0;

            // PCI Express Link Status Register - PE_LSTS [p.355]
            const int PE_LSTS = 0x0E2;

            // PCI Express Slot Capabilities Register - PE_SCAP [p.356]
            const int PE_SCAP = 0x0E4;

            // PCI Express Slot Control Register - PE_SCR [p.357]
            const int PE_SCR = 0x0E8;

            // PCI Express Slot Status Register - PE_SSTS [p.358]
            const int PE_SSTS = 0x0EA;

            // PCI Express Root Control Register - PE_RCR [p.359]
            const int PE_RCR = 0x0EC;

            // PCI Express Root Status Register - PE_RSR [p.360]
            const int PE_RSR = 0x0F0;

            // PCI Express Advanced Error Capability Identifier - ADVERR_CAPID [p.361]
            const int ADVERR_CAPID = 0x100;

            // PCI Express Uncorrectable Error Status - ERRUNC_STS [p.362]
            const int ERRUNC_STS = 0x104;

            // PCI Express Uncorrectable Error Mask - ERRUNC_MSK [p.363]
            const int ERRUNC_MSK = 0x108;

            // PCI Express Uncorrectable Error Severity - ERRUNC_SEV [p.364]
            const int ERRUNC_SEV = 0x10C;

            // PCI Express Correctable Error Status - ERRCOR_STS [p.365]
            const int ERRCOR_STS = 0x110;

            // PCI Express Correctable Error Mask - ERRCOR_MSK [p.366]
            const int ERRCOR_MSK = 0x114;

            // Advanced Error Control and Capability Register - ADVERR_CTL [p.367]
            const int ADVERR_CTL = 0x118;

            // PCI Express Advanced Error Header Log - ADVERR_LOG0 [p.367]
            const int ADVERR_LOG0 = 0x11C;

            // PCI Express Advanced Error Header Log - ADVERR_LOG1 [p.368]
            const int ADVERR_LOG1 = 0x120;

            // PCI Express Advanced Error Header Log - ADVERR_LOG2 [p.368]
            const int ADVERR_LOG2 = 0x124;

            // PCI Express Advanced Error Header Log - ADVERR_LOG3 [p.369]
            const int ADVERR_LOG3 = 0x128;

            // Root Error Command Register - RERR_CMD [p.369]
            const int RERR_CMD = 0x12C;

            // Root Error Status Register - RERR_SR [p.370]
            const int RERR_SR = 0x130;

            // Error Source Identification Register - RERR_ID [p.371]
            const int RERR_ID = 0x134;

            // Device Serial Number Capability - DSN_CAP [p.371]
            const int DSN_CAP = 0x1E0;

            // Device Serial Number Lower DW Register - DSN_LDW [p.372]
            const int DSN_LDW = 0x1E4;

            // Device Serial Number Upper DW Register - DSN_UDW [p.372]
            const int DSN_UDW = 0x1E8;

            // PCI Express Advisory Error Control Register - PIE_AEC [p.373]
            const int PIE_AEC = 0x1EC;

            // Power Budgeting Enhanced Capability Header - PWRBGT_CAPID [p.374]
            const int PWRBGT_CAPID = 0x1F0;

            // Power Budgeting Data Select Register - PWRBGT_DSEL [p.374]
            const int PWRBGT_DSEL = 0x1F4;

            // Power Budgeting Data Register - PWRBGT_DATA [p.375]
            const int PWRBGT_DATA = 0x1F8;

            // Power Budgeting Capability Register - PWRBGT_CAP [p.376]
            const int PWRBGT_CAP = 0x1FC;

            // Outbound I/O Base Address Register - OIOBAR [p.378]
            const int OIOBAR = 0x300;

            // Outbound I/O Window Translate Value Register - OIOWTVR [p.379]
            const int OIOWTVR = 0x304;

            // Outbound Upper Memory Window Base Address Register 0 - OUMBAR0 [p.380]
            const int OUMBAR0 = 0x308;

            // Outbound Upper 32-bit Memory Window Translate Value Register 0 - OUMWTVR0 [p.381]
            const int OUMWTVR0 = 0x30C;

            // Outbound Upper Memory Window Base Address Register 1 - OUMBAR1 [p.382]
            const int OUMBAR1 = 0x310;

            // Outbound Upper 32-bit Memory Window Translate Value Register 1 - OUMWTVR1 [p.383]
            const int OUMWTVR1 = 0x314;

            // Outbound Upper Memory Window Base Address Register 2 - OUMBAR2 [p.384]
            const int OUMBAR2 = 0x318;

            // Outbound Upper 32-bit Memory Window Translate Value Register 2 - OUMWTVR2 [p.385]
            const int OUMWTVR2 = 0x31C;

            // Outbound Upper Memory Window Base Address Register 3 - OUMBAR3 [p.386]
            const int OUMBAR3 = 0x320;

            // Outbound Upper 32-bit Memory Window Translate Value Register 3 - OUMWTVR3 [p.387]
            const int OUMWTVR3 = 0x324;

            // Outbound Configuration Cycle Address Register - OCCAR [p.388]
            const int OCCAR = 0x32C;

            // Outbound Configuration Cycle Data Register - OCCDR [p.389]
            const int OCCDR = 0x330;

            // Outbound Configuration Cycle Function Number - OCCFN [p.390]
            const int OCCFN = 0x334;

            // Inbound Vendor Message Header Register 0 - IVMHR0 [p.391]
            const int IVMHR0 = 0x340;

            // Inbound Vendor Message Header Register 1 - IVMHR1 [p.392]
            const int IVMHR1 = 0x344;

            // Inbound Vendor Message Header Register 2 - IVMHR2 [p.393]
            const int IVMHR2 = 0x348;

            // Inbound Vendor Message Header Register 3 - IVMHR3 [p.394]
            const int IVMHR3 = 0x34C;

            // Inbound Vendor Message Payload Register - IVMPR [p.394]
            const int IVMPR = 0x350;

            // Outbound Vendor Message Header Register 0 - OVMHR0 [p.395]
            const int OVMHR0 = 0x360;

            // Outbound Vendor Message Header Register 1 - OVMHR1 [p.396]
            const int OVMHR1 = 0x364;

            // Outbound Vendor Message Header Register 2 - OVMHR2 [p.397]
            const int OVMHR2 = 0x368;

            // Outbound Vendor Message Header Register 3 - OVMHR3 [p.397]
            const int OVMHR3 = 0x36C;

            // Outbound Vendor Message Payload Register - OVMPR [p.398]
            const int OVMPR = 0x370;

            // PCI Interface Error Control and Status Register - PIE_CSR [p.399]
            const int PIE_CSR = 0x380;

            // PCI Interface Error Status - PIE_STS [p.400]
            const int PIE_STS = 0x384;

            // PCI Interface Error Mask - PIE_MSK [p.401]
            const int PIE_MSK = 0x388;

            // PCI Interface Error Header Log - PIE_LOG0 [p.402]
            const int PIE_LOG0 = 0x38C;

            // PCI Interface Error Header Log 1 - PIE_LOG1 [p.402]
            const int PIE_LOG1 = 0x390;

            // PCI Interface Error Header Log 2 - PIE_LOG2 [p.403]
            const int PIE_LOG2 = 0x394;

            // PCI Interface Error Header Log - PIE_LOG3 [p.403]
            const int PIE_LOG3 = 0x398;

            // PCI Interface Error Descriptor Log - PIE_DLOG [p.404]
            const int PIE_DLOG = 0x39C;

            // ATU Reset Control Register - ATURCR [p.404]
            const int ATURCR = 0x3B0;
        }
    }
}
