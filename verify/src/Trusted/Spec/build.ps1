$ROOT="..\..\.."

. $ROOT\def.ps1

$OBJ = "$OBJROOT\Trusted\Spec\"

$GcVarsCp = "CurrentStack, `$gcSlice, BF, BT, HeapLo, Fi, Fk, Fl, Ti, Tj, Tk, Tl"
$GcVarsMs = "CurrentStack, `$gcSlice, `$color, StackTop, `$fs, `$fn, CachePtr, CacheSize, ColorBase, HeapLo, HeapHi, ReserveMin"

$AllGcVars = "GcVars, `$stackState, `$r1, `$r2, `$freshAbs, `$Time"
$FrameVars = "`$FrameCounts, `$FrameAddrs, `$FrameLayouts, `$FrameSlices, `$FrameAbss, `$FrameOffsets"
$_memVars = "`$sMem, `$dMem, `$pciMem, `$tMems, `$fMems, `$gcMem"
$__MemVars = "SLo, DLo, PciLo, TLo, FLo, GcLo, GcHi"
$MemVars = "`$Mem, $_memVars, $__MemVars"
$IoVars = "`$IoMmuEnabled, `$PciConfigState, DmaAddr"

function preprocess($GcVars, $s)
{
    $s.Replace("AllGcVars", $AllGcVars).Replace("GcVars", $GcVars).Replace("`$FrameVars", $FrameVars).Replace("`$memVars", $_memVars).Replace("`$MemVars", $MemVars).Replace("MemVars", $__MemVars).Replace("`$IoVars", $IoVars)
}

function _catpp([Parameter(Mandatory=$true)]$GcVars, [Parameter(Mandatory=$true)]$out, [Parameter(Mandatory=$true)][string[]]$in)
{
    $ins = $in
    if (needToBuild $out $ins)
    {
        ensureDirForFile($out);
        "catpp -out $out -in $in"
        cat $in | %{preprocess -GcVars $GcVars -s $_} | out-file -encoding ascii $out
        if($LastExitCode)
        {
            throw "error building $out"
        }
    }
}

_catpp -GcVars $GcVarsMs -out $OBJ\CollectorMS_i.bpl -in NucleusInvMarkSweep_i.bpl, Gc_i.bpl
_catpp -GcVars $GcVarsCp -out $OBJ\CollectorCP_i.bpl -in NucleusInvCopying_i.bpl,   Gc_i.bpl
_catpp -GcVars $GcVarsMs -out $OBJ\EntryMS_i.bpl -in Entry_i.bpl
_catpp -GcVars $GcVarsCp -out $OBJ\EntryCP_i.bpl -in Entry_i.bpl

