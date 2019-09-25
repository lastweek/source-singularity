$ROOT="..\..\..\.."

. $ROOT\def.ps1

$OBJ = "$OBJROOT\Checked\Nucleus\GC"
$SPEC_OBJ = "$OBJROOT\Trusted\Spec"

$SPECS = list $SPEC\base_i.bpl $SPEC\memory_i.bpl $SPEC\stacks_i.bpl $SPEC\assembly_i.bpl $SPEC\bartok_i.bpl $SPEC\Io_i.bpl
$AXIOMS = list $SPEC\base_axioms.bpl $SPEC\memory_axioms.bpl $SPEC\stacks_axioms.bpl $SPEC\assembly_axioms.bpl $SPEC\bartok_axioms.bpl

$BASE = "$OBJ\..\Base"
$BASES = list $BASE\overflow_i.bpl $BASE\util_i.bpl $BASE\separation_i.bpl

_beat   -out $OBJ\Reach_i.bpl -in Reach_i.beat
_beat   -out $OBJ\Reach.bpl   -in Reach.beat
_beat   -out $OBJ\Common_i.bpl -in Common_i.beat -includes ..\Base\separation_i.beat
_beat   -out $OBJ\Common.bpl   -in Common.beat   -includes ..\Base\separation_i.beat

_beat   -out $OBJ\MarkSweepCollector__i.bpl -in MarkSweepCollector_i.beat -includes ..\Base\separation_i.beat, $SPEC_OBJ\CollectorMS_i.bpl
_cat    -out $OBJ\MarkSweepCollector_i.bpl  -in $SPEC_OBJ\CollectorMS_i.bpl, $OBJ\MarkSweepCollector__i.bpl
_beat   -out $OBJ\MarkSweepCollector.bpl    -in MarkSweepCollector.beat   -includes ..\Base\separation_i.beat, $SPEC_OBJ\CollectorMS_i.bpl, MarkSweepCollector_i.beat

_beat   -out $OBJ\CopyingCollector__i.bpl   -in CopyingCollector_i.beat  -includes ..\Base\separation_i.beat, $SPEC_OBJ\CollectorCP_i.bpl
_cat    -out $OBJ\CopyingCollector_i.bpl    -in $SPEC_OBJ\CollectorCP_i.bpl, $OBJ\CopyingCollector__i.bpl
_beat   -out $OBJ\CopyingCollector.bpl      -in CopyingCollector.beat    -includes ..\Base\separation_i.beat, $SPEC_OBJ\CollectorCP_i.bpl, CopyingCollector_i.beat

_boogie -out $OBJ\BitVectorsBuiltin_i.v /bv:z $SPEC\base_i.bpl $SPEC\memory_i.bpl $SPEC\assembly_axioms.bpl $SPEC\BitVectorsBuiltin_i.bpl BitVectorsBuiltin_i.bpl
_boogie -out $OBJ\BitVectorsBuiltin.v   /bv:z $SPEC\base_i.bpl $SPEC\memory_i.bpl $SPEC\assembly_axioms.bpl $SPEC\BitVectorsBuiltin_i.bpl BitVectorsBuiltin_i.bpl $SPEC\BitVectors_axioms.bpl BitVectorsBuiltin.bpl
_boogie -out $OBJ\BitVectors_i.v       $SPEC\assembly_axioms.bpl $SPEC\base_i.bpl $SPEC\memory_i.bpl $SPEC\BitVectors_i.bpl BitVectors_i.bpl
_boogie -out $OBJ\BitVectors.v   /bv:z $SPEC\assembly_axioms.bpl $SPEC\base_i.bpl $SPEC\memory_i.bpl $SPEC\BitVectors_i.bpl BitVectors_i.bpl BitVectorsBuiltin_i.bpl $SPEC\BitVectors_axioms.bpl BitVectors.bpl
_boogie -out $OBJ\Reach_i.v $SPECS $AXIOMS $BASES $OBJ\Reach_i.bpl
_boogie -out $OBJ\Reach.v   $SPECS $AXIOMS $BASES $OBJ\Reach_i.bpl $OBJ\Reach.bpl
_boogie -out $OBJ\Common_i.v $SPECS $AXIOMS $BASES BitVectors_i.bpl $OBJ\Reach_i.bpl $OBJ\Common_i.bpl
_boogie -out $OBJ\Common.v   $SPECS $AXIOMS $BASES BitVectors_i.bpl $OBJ\Reach_i.bpl $OBJ\Common_i.bpl $OBJ\Common.bpl
_boogie -out $OBJ\MarkSweepCollector_i.v $SPECS $AXIOMS $BASES BitVectors_i.bpl $OBJ\Reach_i.bpl $OBJ\Common_i.bpl $OBJ\MarkSweepCollector_i.bpl
_boogie -out $OBJ\MarkSweepCollector.v   $SPECS $AXIOMS $BASES BitVectors_i.bpl $OBJ\Reach_i.bpl $OBJ\Common_i.bpl $OBJ\MarkSweepCollector_i.bpl $OBJ\MarkSweepCollector.bpl
_boogie -out $OBJ\CopyingCollector_i.v $SPECS $AXIOMS $BASES BitVectors_i.bpl $OBJ\Reach_i.bpl $OBJ\Common_i.bpl $OBJ\CopyingCollector_i.bpl
_boogie -out $OBJ\CopyingCollector.v   $SPECS $AXIOMS $BASES BitVectors_i.bpl $OBJ\Reach_i.bpl $OBJ\Common_i.bpl $OBJ\CopyingCollector_i.bpl $OBJ\CopyingCollector.bpl
