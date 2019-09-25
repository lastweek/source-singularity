typedef __int64 Gdte;
typedef unsigned char byte;
typedef unsigned short ushort;
typedef unsigned uint;
typedef unsigned __int64 ulong;
typedef ULONG_PTR UIntPtr;

const int Class_Microsoft_Singularity_Hal_Platform_EXIT_AND_RESTART     = 0x1fff;
const int Class_Microsoft_Singularity_Hal_Platform_EXIT_AND_SHUTDOWN    = 0x1ffe;
const int Class_Microsoft_Singularity_Hal_Platform_EXIT_AND_WARMBOOT    = 0x1ffd;
const int Class_Microsoft_Singularity_Hal_Platform_EXIT_AND_HALT        = 0x1ffc;
const int            Class_Microsoft_Singularity_Hal_Platform_DEBUGGER_NONE       = 0;
const int            Class_Microsoft_Singularity_Hal_Platform_DEBUGGER_SERIAL     = 1;
const int            Class_Microsoft_Singularity_Hal_Platform_DEBUGGER_1394       = 2;

struct Class_Microsoft_Singularity_MpBootInfo
{
    uint     signature;
    UIntPtr  KernelStackBegin;
    UIntPtr  KernelStack;
    UIntPtr  KernelStackLimit;
    volatile int TargetCpu;
};

struct Struct_Microsoft_Singularity_Isal_IX_DescriptorTable_Gdt
{
    Gdte     nul;    
    Gdte    pv;     
    Gdte    rc;     
    Gdte    rd;     
    Gdte    pc;     
    Gdte    pd;     
    Gdte    lc;     
    Gdte    ld;     
    Gdte     uc;     
    Gdte     ud;     
    Gdte     pp;     
    Gdte     nn;     
    Gdte        tss;        
};

struct Struct_Microsoft_Singularity_Isal_IX_Gdtp
{
    ushort     pad;
    ushort     limit;
    uint       addr;
};

struct Struct_Microsoft_Singularity_Isal_IX_DescriptorTable
{
    Struct_Microsoft_Singularity_Isal_IX_DescriptorTable_Gdt              gdt;
    Struct_Microsoft_Singularity_Isal_IX_Gdtp             gdtPtr;
};

struct Class_Microsoft_Singularity_Hal_Cpu
{
    int        Size;
    int        Id;
    UIntPtr     CpuRecordPage;
    UIntPtr     KernelStackLimit; 
    UIntPtr     KernelStackBegin; 
    int         DomainBsp;
    Struct_Microsoft_Singularity_Isal_IX_DescriptorTable                     segments;
    bool halted;
};

struct Class_Microsoft_Singularity_Hal_Platform
{
    
    int         Size;
    uint        BootYear;
    uint        BootMonth;
    uint        BootDay;
    uint        BootHour;
    uint        BootMinute;
    uint        BootSecond;
    int         CpuMaxCount;
    int         CpuRealCount;
    int         BootCount;
    UIntPtr     Smap32;
    int         SmapCount;
    UIntPtr     PhysicalBase;
    uint*OutgoingMessage;
    int* OutgoingCount;
    uint*IncomingFree;       
    int* IncomingFreeCount;
    uint*IncomingMessage;    
    int* IncomingCount;
    uint*OutgoingFree;       
    int* OutgoingFreeCount;
    uint        MaxBufferLength;
     uint       thisDestinationId;
     uint       hasApic;
    UIntPtr     BootAllocatedMemory;
    UIntPtr     BootAllocatedMemorySize;
    UIntPtr     CommandLine32;
    int         CommandLineCount;
    int  CpuRecordPointerOffset;
    int  ThreadRecordPointerOffset;
    UIntPtr     LogRecordBuffer;
    UIntPtr     LogRecordSize;
    UIntPtr     LogTextBuffer;
    UIntPtr     LogTextSize;
    UIntPtr     KernelDllBase;
    UIntPtr     KernelDllSize;
    UIntPtr     KernelDllFirstPage; 
    UIntPtr     MiniDumpBase;
    UIntPtr     MiniDumpLimit;
    int         DebuggerType;

    uint     RecSize;
    ushort   DebugBasePort;
    ushort   DebugSpinBase;
    uint     TwiddleSpinBase;
    ulong    Info32;
    ulong    Kill32;
    uint     KillAction;
    ulong    DumpAddr32;
    ulong    FileImageTableBase32;
    uint     FileImageTableEntries;
    uint     DumpSize32;
    ulong    DumpRemainder;
    ulong    DumpLimit;
    ulong    NativeContext;
    ulong    Cpus;
    ushort   BiosPicMask;
    byte     BiosWarmResetCmos;
    uint     BiosWarmResetVector;
    uint     Info16;
    ulong    IdtEnter0;
    ulong    IdtEnter1;
    ulong    IdtEnterN;
    ulong    IdtTarget;
    ulong    Pdpt32;
    ulong    KernelPdpt64;
    ulong    Undump;
    uint     PciBiosAX;
    uint     PciBiosBX;
    uint     PciBiosCX;
    uint     PciBiosEDX;
    ulong    AcpiRoot32;
    ulong    PnpNodesAddr32;
    uint     PnpNodesSize32;
    ulong    SmbiosRoot32;
    ulong    DmiRoot32;
    uint     IsaCsns;
    ushort   IsaReadPort;
    uint     Ebda32;
    uint     MpFloat32;
    ulong    Ohci1394Base;
    ulong    Ohci1394BufferAddr32;
    uint     Ohci1394BufferSize32;
    ulong    VesaBuffer;
    ulong    MpEnter32;          
    uint     MpCpuCount;         
    uint     MpStatus32;         
    ulong    MpStartupLock32;    
    Class_Microsoft_Singularity_MpBootInfo   MpBootInfo;


};

struct Struct_Microsoft_Singularity_Io_FileImage
{
    UIntPtr Address;
    uint    Size;
};

struct Struct_Microsoft_Singularity_Isal_IX_TSS
{
    ushort     previous_tss;
    ushort     pad0;

    uint       esp0;
    ushort     ss0;
    ushort     pad1;

    uint       esp1;
    ushort     ss1;
    ushort     pad2;

    uint       esp2;
    ushort     ss2;
    ushort     pad3;

    uint       cr3;
    uint       eip;
    uint       eflags;

    uint       eax;
    uint       ecx;
    uint       edx;
    uint       ebx;
    uint       esp;
    uint       ebp;
    uint       esi;
    uint       edi;

    ushort     es;
    ushort     pades;
    ushort     cs;
    ushort     padcs;
    ushort     ss;
    ushort     padss;
    ushort     ds;
    ushort     padds;
    ushort     fs;
    ushort     padfs;
    ushort     gs;
    ushort     padgs;

    ushort     ldt;
    ushort     padldt;
    ushort     trap_bit;
    ushort     io_bitmap_offset;
};
