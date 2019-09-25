$ROOT="..\..\..\.."

. $ROOT\def.ps1

$OBJ = "$OBJROOT\Checked\Nucleus\Main"
$SPEC_OBJ = "$OBJROOT\Trusted\Spec"

$SPECS = list $SPEC\base_i.bpl $SPEC\memory_i.bpl $SPEC\stacks_i.bpl $SPEC\assembly_i.bpl $SPEC\bartok_i.bpl $SPEC\Interrupts_i.bpl $SPEC\Io_i.bpl
$AXIOMS = list $SPEC\base_axioms.bpl $SPEC\memory_axioms.bpl $SPEC\stacks_axioms.bpl $SPEC\assembly_axioms.bpl $SPEC\bartok_axioms.bpl $SPEC\Io_axioms.bpl

$BASE = "$OBJ\..\Base"
$BASES = list $BASE\overflow_i.bpl $BASE\util_i.bpl $BASE\separation_i.bpl

$GC = "$OBJ\..\GC"

_cat    -out $OBJ\EntryMS_i.bpl -in $SPEC_OBJ\EntryMS_i.bpl
_cat    -out $OBJ\EntryCP_i.bpl -in $SPEC_OBJ\EntryCP_i.bpl

_beat   -out $OBJ\EntryMS.bpl -in Entry.beat          -includes ..\Base\separation_i.beat, ..\GC\MarkSweepCollector_i.beat
_beat   -out $OBJ\EntryCP.bpl -in Entry.beat          -includes ..\Base\separation_i.beat, ..\GC\CopyingCollector_i.beat

_boogie -out $OBJ\EntryMS_i.v $SPECS $AXIOMS $BASES ..\GC\BitVectors_i.bpl $GC\Reach_i.bpl $GC\Common_i.bpl $GC\MarkSweepCollector_i.bpl $OBJ\EntryMS_i.bpl
_boogie -out $OBJ\EntryMS.v   $SPECS $AXIOMS $BASES ..\GC\BitVectors_i.bpl $GC\Reach_i.bpl $GC\Common_i.bpl $GC\MarkSweepCollector_i.bpl $OBJ\EntryMS_i.bpl $SPEC\word_axioms.bpl $OBJ\EntryMS.bpl

_boogie -out $OBJ\EntryCP_i.v $SPECS $AXIOMS $BASES ..\GC\BitVectors_i.bpl $GC\Reach_i.bpl $GC\Common_i.bpl $GC\CopyingCollector_i.bpl   $OBJ\EntryCP_i.bpl
_boogie -out $OBJ\EntryCP.v   $SPECS $AXIOMS $BASES ..\GC\BitVectors_i.bpl $GC\Reach_i.bpl $GC\Common_i.bpl $GC\CopyingCollector_i.bpl   $OBJ\EntryCP_i.bpl $SPEC\word_axioms.bpl $OBJ\EntryCP.bpl
