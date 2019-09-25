//
// Copyright (c) Microsoft Corporation.  All rights reserved.
//

// We model input and output as unbounded streams of input events or output events.

// $VgaEvents is an unbounded stream of events sent to the VGA screen.
// $VgaEvents[0...$VgaNextEvent-1] have already been sent to the screen.
type VgaEvent;
function VgaTextStore($ptr:int, $val:int) returns(VgaEvent);
var $VgaEvents:[int]VgaEvent;
var $VgaNextEvent:int;

const ?VgaTextLo: int; axiom ?VgaTextLo == /*0xb8000*/753664;
const ?VgaTextHi: int; axiom ?VgaTextHi ==            761664;
function vgaAddr2(i:int) returns (bool) {?VgaTextLo <= i && i <= ?VgaTextHi - 2}

procedure VgaTextStore16($ptr:int, $val:int);
  requires vgaAddr2($ptr);
  requires word($val);
  modifies $Eip;
  modifies $VgaNextEvent, $VgaEvents;
  ensures  $VgaNextEvent == old($VgaNextEvent) + 1;
  ensures  $VgaEvents == old($VgaEvents)[old($VgaNextEvent) := VgaTextStore($ptr, $val)];

// For diagnostics, allow arbitrary writes to the first line of the screen.
// (If no diagnostics are needed, this can be disabled.)
procedure VgaDebugStore16($ptr:int, $val:int);
  requires ?VgaTextLo <= $ptr && $ptr <= ?VgaTextLo + 158;
  requires word($val);
  modifies $Eip;

// $KeyboardEvents is an unbounded stream of events from the keyboard.
// $KeyboardEvents[0..$KeyboardDone-1] have already been read from the keyboard.
// $KeyboardEvents[$KeyboardDone..$KeyboardAvailable-1] are ready to read but
// have not yet been read.
var $KeyboardEvents:[int]int;
var $KeyboardAvailable:int;
var $KeyboardDone:int;

procedure KeyboardStatusIn8();
  modifies $Eip, eax, $KeyboardAvailable;
  ensures  and(eax, 1) == 0 ==> $KeyboardAvailable == $KeyboardDone;
  ensures  and(eax, 1) != 0 ==> $KeyboardAvailable > $KeyboardDone;

procedure KeyboardDataIn8();
  requires $KeyboardAvailable > $KeyboardDone;
  modifies $Eip, eax;
  modifies $KeyboardDone;
  ensures  $KeyboardDone == old($KeyboardDone) + 1;
  ensures  and(eax, 255) == $KeyboardEvents[old($KeyboardDone)];

// ACPI tables
const ?RsdpPtr:int;
const ?RsdpExists:bool;
const ?RsdtPtr:int;
const ?RsdtCount:int;
const ?DmarPtr:int;
const ?DmarExists:bool;
const ?DmarLen:int;
const ?DrhdPtr:[int]int;
const ?DrhdCount:int;
const ?DrhdRegs:[int]int;

const ?RoBiosLo:int; axiom ?RoBiosLo ==  917504; //  0xE0000
const ?RoBiosHi:int; axiom ?RoBiosHi == 1048576; // 0x100000
function inBiosRo(i:int) returns(bool) { ?RoBiosLo <= i && i < ?RoBiosHi }

function ByteSum(ptr:int, end:int) returns(int);

function MatchesRsdp(ptr:int) returns(bool)
{
    ro32(ptr + 0) == 541348690 // 0x20445352 "RSD "
 && ro32(ptr + 4) == 542266448 // 0x20525450 "PTR "
 && and(ByteSum(ptr, ptr + 20), 255) == 0
}

function MatchesDmar(ptr:int) returns(bool)
{
    ro32(ptr + 0) == 1380011332 // 0x52414d44 "DMAR"
}

function MatchesDrhd(ptr:int) returns(bool)
{
    roU16(ptr) == 0
}

function MaybeDrhd(ptr:int, entry:int) returns(bool)
{
    ?DrhdPtr[entry] == ptr
 && inRo(ptr + 0, 2)
 && inRo(ptr + 2, 2)
 && ptr + roU16(ptr + 2) <= ?DmarPtr + ?DmarLen
}

function DrhdInv(ptr:int, entry:int) returns(bool)
{
    inRo(ptr + 8, 4)
 && inRo(ptr + 12, 4)
 && (ro32(ptr + 12) == 0 ==> ?DrhdRegs[entry] == ro32(?DrhdPtr[entry] + 8))
}

procedure rsdpExists($ptr:int, $entry:int);
  requires $ptr == ?RoBiosLo + 16 * $entry;
  requires inBiosRo($ptr);
  requires MatchesRsdp($ptr);
  requires (forall j:int::{TV(j)} TV(j) && j < $entry && inBiosRo(?RoBiosLo + 16 * j)
            ==> !MatchesRsdp(?RoBiosLo + 16 * j));
  ensures  ?RsdpExists;
  ensures  ?RsdpPtr == $ptr;

procedure dmarExists($ptr:int, $entry:int);
  requires $ptr == ro32(?RsdtPtr + 36 + 4 * $entry);
  requires ?RsdpExists;
  requires 0 <= $entry && $entry < ?RsdtCount;
  requires MatchesDmar($ptr);
  requires (forall j:int::{TV(j)} TV(j) && 0 <= j && j < ?RsdtCount && $entry != j
             ==> !MatchesDmar(ro32(?RsdtPtr + 36 + 4 * j)));
  ensures  ?DmarExists;
  ensures  ?DmarPtr == $ptr;

procedure drhdExists($ptr:int, $entry:int);
  requires MaybeDrhd($ptr, $entry);
  requires $ptr < ?DmarPtr + ?DmarLen;
  requires MatchesDrhd($ptr);
  ensures  ?DrhdPtr[$entry] == $ptr;
  ensures  MaybeDrhd($ptr + roU16($ptr + 2), $entry + 1);
  ensures  DrhdInv($ptr, $entry);

procedure drhdEnd($ptr:int, $entry:int);
  requires MaybeDrhd($ptr, $entry);
  requires $ptr == ?DmarPtr + ?DmarLen || !MatchesDrhd($ptr);
  ensures  ?DrhdCount == $entry;

// IOMMU, DMA

// Note: iom and dma must be contiguous (?iomHi == ?dmaLo),
// because iom contains the byte[] header for the dma region
const ?iomLo:int;
const ?iomHi:int; axiom ?iomHi == ?iomLo + 65536;
const ?dmaLo:int;
const ?dmaHi:int; axiom ?dmaHi == ?dmaLo + 18 * 1024 * 1024;

function iomAddr(i:int) returns (bool) {?iomLo <= i && i < ?iomHi}
function iomAddrEx(i:int) returns (bool) {?iomLo <= i && i <= ?iomHi}

// $IomMem[i] = data at address i, if iomAddr(i) and Aligned(i).
var $IomMem:[int]int; // Do not modify directly! Use IomStore.
var $IomFrozen:bool;
var $IoMmuState:[int]int;
var $IoMmuEnabled:bool;

procedure IomStore($ptr:int, $val:int);
  requires iomAddr($ptr);
  requires Aligned($ptr);
  requires word($val);
  requires !$IomFrozen;
  modifies $Eip, $IomMem;
  ensures  $IomMem == old($IomMem)[$ptr := $val];

procedure IomRegLoad($entry:int, $ptr:int) returns ($val:int);
  requires $ptr == ?DrhdRegs[$entry] + 28
        || $ptr == ?DrhdRegs[$entry] + 0
        || $ptr == ?DrhdRegs[$entry] + 8
        || $ptr == ?DrhdRegs[$entry] + 12;
  modifies $Eip;
  ensures  word($val);

// TODO: invalidate context-cache and IOTLB?
procedure IomRegStore($entry:int, $ptr:int, $val:int);
  requires ($IoMmuState[$entry] == 0 && $ptr == ?DrhdRegs[$entry] + 32 && IoRootTable($IomMem, $val))
        || ($IoMmuState[$entry] == 1 && $ptr == ?DrhdRegs[$entry] + 36 && $val == 0)
        || ($IoMmuState[$entry] == 2 && $ptr == ?DrhdRegs[$entry] + 24 && $val == shl(1, 30))
        || ($IoMmuState[$entry] == 3 && $ptr == ?DrhdRegs[$entry] + 24 && $val == shl(1, 31));
  modifies $Eip, $IoMmuState, $IomFrozen;
  ensures  $IoMmuState == old($IoMmuState)[$entry := 1 + old($IoMmuState)[$entry]];
  ensures  $IomFrozen;

procedure iomEnable();
  requires (forall i:int::{$IoMmuState[i]} 0 <= i && i < ?DrhdCount ==> $IoMmuState[i] == 4);
  requires $IomMem[?dmaLo - 8] == ?BYTE_VECTOR_VTABLE; // byte[].VTable
  requires $IomMem[?dmaLo - 4] == ?dmaHi - ?dmaLo; // byte[].Length
  modifies $IoMmuEnabled;
  ensures  $IoMmuEnabled;

// Does physical page n fit inside dma area?  If so, we can map it.
function IsDmaPage(ptr:int) returns(bool)
{
    and(ptr, 4095) == 0
 && ?dmaLo <= ptr && ptr + 4096 <= ?dmaHi
}

function IoPageTableEntry(w0:int, w1:int) returns(bool)
{
    w1 == 0 && (w0 == 0 || IsDmaPage(w0 - 3))
}

function{:expand false} IoPageTable($IomMem:[int]int, ptr:int) returns(bool)
{
    and(ptr, 4095) == 0
 && (forall i:int::{TV(i)} TV(i) && 0 <= i && i < 512 ==>
      IoPageTableEntry($IomMem[ptr + 8 * i], $IomMem[ptr + 8 * i + 4]))
}

function IoPageDirEntry($IomMem:[int]int, w0:int, w1:int) returns(bool)
{
    w1 == 0 && (w0 == 0 || IoPageTable($IomMem, w0 - 3))
}

function{:expand false} IoPageDir($IomMem:[int]int, ptr:int) returns(bool)
{
    and(ptr, 4095) == 0
 && (forall i:int::{TV(i)} TV(i) && 0 <= i && i < 512 ==>
      IoPageDirEntry($IomMem, $IomMem[ptr + 8 * i], $IomMem[ptr + 8 * i + 4]))
}

function{:expand false} IoPageDirStub($IomMem:[int]int, ptr:int) returns(bool)
{
    and(ptr, 4095) == 0
 && $IomMem[ptr + 4] == 0
 && (forall i:int::{TV(i)} TV(i) && 1 <= i && i < 512 ==>
      $IomMem[ptr + 8 * i] == 0 && $IomMem[ptr + 8 * i + 4] == 0)
}

function IoContextEntry($IomMem:[int]int, w0:int, w1:int, w2:int, w3:int) returns(bool)
{
    w3 == 0 && w2 == 258 && w1 == 0
 && IoPageDirStub($IomMem, w0 - 3)
 && IoPageDirStub($IomMem, $IomMem[w0 - 3] - 3)
 && IoPageDir($IomMem, $IomMem[$IomMem[w0 - 3] - 3] - 3)
}

function{:expand false} IoContextTable($IomMem:[int]int, ptr:int) returns(bool)
{
    and(ptr, 4095) == 0
 && (forall i:int::{TV(i)} TV(i) && 0 <= i && i < 256 ==>
      IoContextEntry($IomMem,
        $IomMem[ptr + 16 * i + 0],
        $IomMem[ptr + 16 * i + 4],
        $IomMem[ptr + 16 * i + 8],
        $IomMem[ptr + 16 * i + 12]))
}

function IoRootEntry($IomMem:[int]int, w0:int, w1:int, w2:int, w3:int) returns(bool)
{
    w3 == 0 && w2 == 0 && w1 == 0 && IoContextTable($IomMem, w0 - 1)
}

function{:expand false} IoRootTable($IomMem:[int]int, ptr:int) returns(bool)
{
    and(ptr, 4095) == 0
 && (forall i:int::{TV(i)} TV(i) && 0 <= i && i < 256 ==>
      IoRootEntry($IomMem,
        $IomMem[ptr + 16 * i + 0],
        $IomMem[ptr + 16 * i + 4],
        $IomMem[ptr + 16 * i + 8],
        $IomMem[ptr + 16 * i + 12]))
}



// PCI

function IsValidPciId(id:int) returns(bool) {
  0 <= id && id < 65536
}
function IsValidPciOffset(o:int) returns(bool) {
  0 <= o && o < 256 && Aligned(o)
}

// Note: these three functions record the fact that some read/load/store
// occured at some time.  We could make them more precise by recording the
// exact time (or some sequence number).
function PciConfigReadResult(id:int, offset:int, val:int) returns(bool);
function PciMemLoaded(id:int, ptr:int, val:int) returns(bool);
function PciMemStored(id:int, ptr:int, val:int) returns(bool);

function PciMemAddr(id:int) returns(int);
function PciMemSize(id:int) returns(int);

const ?FFFFFFFF:int;
axiom ?FFFFFFFF == 2147483647 + 2147483647 + 1 /*0xffffffff*/;

var $PciConfigId:int;
var $PciConfigOffset:int;

// $PciConfigState[id] in {0,1,2,3,4}
//   0 ==> start state
//   1 ==> memory space disabled
//   2 ==> BAR set to 0xffffffff
//   3 ==> BAR set to address
//   4 ==> memory space enabled
var $PciConfigState:[int]int;

function PciVendorId(config0:int) returns(int) { and(config0, 65535) }
function PciHeaderType(config12:int) returns(int) { and(shr(config12, 16), 255) }

procedure PciConfigAddrOut32($id:int, $offset:int);
  requires eax == or(or(shl($id, 8), $offset), 2147483647 + 1 /*0x80000000*/);
  requires edx == 3320 /* 0xcf8 */;
  requires IsValidPciId($id);
  requires IsValidPciOffset($offset);
  modifies $Eip;
  modifies $PciConfigId, $PciConfigOffset;
  ensures  $PciConfigId == $id;
  ensures  $PciConfigOffset == $offset;

procedure PciConfigDataIn32($id:int, $offset:int);
  requires $id == $PciConfigId;
  requires $offset == $PciConfigOffset;
  requires edx == 3324 /* 0xcfc */;
  requires IsValidPciId($id);
  requires IsValidPciOffset($offset);
  modifies $Eip, eax;
  modifies $PciConfigId, $PciConfigOffset;
  ensures  PciConfigReadResult($id, $offset, eax);
  ensures  $PciConfigState[$id] == 0 && $offset == 16 && and(eax, 15) == 0 ==> PciMemAddr($id) == eax;
  ensures  $PciConfigState[$id] == 2 && $offset == 16                      ==> PciMemSize($id) == 1 + neg(eax);
  ensures  word(eax);

procedure PciConfigDataOut32($id:int, $offset:int, $config0:int, $config4:int, $config12:int, $config16:int);
  requires $id == $PciConfigId;
  requires $offset == $PciConfigOffset;
  requires edx == 3324 /* 0xcfc */;
  requires IsValidPciId($id);
  requires IsValidPciOffset($offset);
  requires and($id, 7) == 0; // support only function 0 for now
  requires PciConfigReadResult($id,  0, $config0);
  requires PciConfigReadResult($id,  4, $config4);
  requires PciConfigReadResult($id, 12, $config12);
  requires PciConfigReadResult($id, 16, $config16);
  requires PciVendorId($config0) != 65535;
  requires PciHeaderType($config12) == 0;
  requires $PciConfigState[$id] == 0 ==> $offset == 4  && eax == and($config4, ?FFFFFFFF - 2);
  requires $PciConfigState[$id] == 1 ==> $offset == 16 && eax == ?FFFFFFFF;
  requires $PciConfigState[$id] == 2 ==> $offset == 16 && eax == PciMemAddr($id);
  requires $PciConfigState[$id] == 3 ==> $offset == 4  && eax == or($config4, 2);
  requires $PciConfigState[$id] != 4;
  modifies $Eip;
  modifies $PciConfigId, $PciConfigOffset, $PciConfigState;
  ensures  $PciConfigState == old($PciConfigState)[$id := 1 + old($PciConfigState)[$id]];

procedure PciMemLoad32($id:int, $ptr:int) returns($val:int);
  requires $IoMmuEnabled;
  requires $PciConfigState[$id] == 4;
  requires PciMemAddr($id) <= $ptr && $ptr + 4 <= PciMemAddr($id) + PciMemSize($id);
  modifies $Eip;
  ensures  PciMemLoaded($id, $ptr, $val);
  ensures  word($val);

procedure PciMemStore32($id:int, $ptr:int, $val:int);
  requires $IoMmuEnabled;
  requires $PciConfigState[$id] == 4;
  requires PciMemAddr($id) <= $ptr && $ptr + 4 <= PciMemAddr($id) + PciMemSize($id);
  requires word($val);
  modifies $Eip;
  ensures  PciMemStored($id, $ptr, $val);

