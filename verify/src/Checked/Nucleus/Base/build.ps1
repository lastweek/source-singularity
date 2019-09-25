$ROOT="..\..\..\.."

. $ROOT\def.ps1

$OBJ = "$OBJROOT\Checked\Nucleus\Base"

$SPECS = list $SPEC\base_i.bpl $SPEC\memory_i.bpl $SPEC\stacks_i.bpl $SPEC\assembly_i.bpl $SPEC\bartok_i.bpl $SPEC\Interrupts_i.bpl $SPEC\Io_i.bpl
$AXIOMS = list $SPEC\base_axioms.bpl $SPEC\memory_axioms.bpl $SPEC\stacks_axioms.bpl $SPEC\assembly_axioms.bpl $SPEC\bartok_axioms.bpl

_copy   -out $OBJ\Util_i.bpl -in Util_i.bpl
_beat   -out $OBJ\Util.bpl   -in Util.beat
_copy   -out $OBJ\Overflow_i.bpl -in $SPEC\Overflow_i.bpl
_beat   -out $OBJ\Overflow.bpl   -in Overflow.beat
_beat   -out $OBJ\Separation_i.bpl -in Separation_i.beat
_beat   -out $OBJ\Separation.bpl   -in Separation.beat -includes separation_i.beat

_boogie -out $OBJ\Util_i.v $SPECS $AXIOMS $OBJ\Util_i.bpl
_boogie -out $OBJ\Util.v   $SPECS $AXIOMS $OBJ\Util_i.bpl $SPEC\word_axioms.bpl $OBJ\Util.bpl
_boogie -out $OBJ\Overflow_i.v $SPECS $AXIOMS $OBJ\Util_i.bpl $OBJ\Overflow_i.bpl
_boogie -out $OBJ\Overflow.v   $SPECS $AXIOMS $OBJ\Util_i.bpl $OBJ\Overflow_i.bpl $SPEC\word_axioms.bpl $OBJ\Overflow.bpl
_boogie -out $OBJ\Separation_i.v $SPECS $AXIOMS $OBJ\Util_i.bpl $OBJ\Separation_i.bpl
_boogie -out $OBJ\Separation.v   $SPECS $AXIOMS $OBJ\Util_i.bpl $OBJ\Separation_i.bpl $SPEC\word_axioms.bpl $OBJ\Separation.bpl
