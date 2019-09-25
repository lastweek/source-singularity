$ROOT="..\..\.."

. $ROOT\def.ps1

runShell "cd Base; .\build.ps1"
runShell "cd GC; .\build.ps1"
runShell "cd Main; .\build.ps1"

$OBJ = "$OBJROOT\Checked\Nucleus\"

_boogieasm -out $OBJ\nucleus_ms.asm $SPEC\base $SPEC\memory $SPEC\assembly $SPEC\stacks $SPEC\interrupts $SPEC\io $SPEC\bartok $SPEC\BitVectors $OBJ\Base\Util $OBJ\Base\Overflow $OBJ\Base\Separation GC\BitVectorsBuiltin GC\BitVectors $OBJ\GC\Reach $OBJ\GC\Common $OBJ\GC\MarkSweepCollector $OBJ\Main\EntryMS
_boogieasm -out $OBJ\nucleus_cp.asm $SPEC\base $SPEC\memory $SPEC\assembly $SPEC\stacks $SPEC\interrupts $SPEC\io $SPEC\bartok $SPEC\BitVectors $OBJ\Base\Util $OBJ\Base\Overflow $OBJ\Base\Separation GC\BitVectorsBuiltin GC\BitVectors $OBJ\GC\Reach $OBJ\GC\Common $OBJ\GC\CopyingCollector   $OBJ\Main\EntryCP

