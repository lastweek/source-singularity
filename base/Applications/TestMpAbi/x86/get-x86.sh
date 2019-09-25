#!/bin/sh

echo ""
echo "  Getting kernel.x86"
cp ../../../Kernel/obj/Prototype.ApicMP.Min.MarkSweep/kernel.x86 ./

echo ""
echo "  Getting TestMpAbi.x86"
cp ../../../Distro/obj/Prototype.ApicMP.Min.MarkSweep.Prototype.MarkSweep/Singularity/Binaries/TestMpAbi.x86 ./

echo ""
echo "  Getting MpSyscalls.x86"
cp ../../../Kernel/obj/Prototype.ApicMP.Min.MarkSweep/MpSyscalls.x86 ./

echo ""





