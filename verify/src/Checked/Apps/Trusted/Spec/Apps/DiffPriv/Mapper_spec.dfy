include "../../Assembly.dfy"
include "../../../../Checked/Libraries/Math/power2.dfy"
include "Database_spec.dfy"

///////////////////////////////////////////
// Binary instructions
///////////////////////////////////////////

datatype BinaryInstruction = InstAdd | InstSub | InstMul | InstDiv | InstMod | InstGt | InstLt | InstEq | InstGe | InstLe

function method BooleanToWord(b:bool):int
    ensures Word32(BooleanToWord(b));
{
    lemma_2toX();
    if b then 1 else 0
}

function method ApplyBinaryInstruction(inst:BinaryInstruction, v1:int, v2:int):int
    requires Word32(v1);
    requires Word32(v2);
    ensures Word32(ApplyBinaryInstruction(inst, v1, v2));
{
    match inst
        case InstAdd => AddInstruction(v1, v2)
        case InstSub => SubInstruction(v1, v2)
        case InstMul => MulInstruction(v1, v2)
        case InstDiv => if v2 == 0 then 0 else DivInstruction(v1, v2)
        case InstMod => if v2 == 0 then 0 else ModInstruction(v1, v2)
        case InstGt => BooleanToWord(v1 > v2)
        case InstLt => BooleanToWord(v1 < v2)
        case InstEq => BooleanToWord(v1 == v2)
        case InstGe => BooleanToWord(v1 >= v2)
        case InstLe => BooleanToWord(v1 <= v2)
}

///////////////////////////////////////////
// Expressions
///////////////////////////////////////////

datatype Expression = ExpInt(i:int)
                    | ExpColumn(col:Expression)
                    | ExpBinary(inst:BinaryInstruction, e1:Expression, e2:Expression)
                    | ExpIf(e_cond:Expression, e_true:Expression, e_false:Expression)

function ExpressionValid(e:Expression):bool
{
    match e
        case ExpInt(i) => Word32(i)
        case ExpColumn(e1) => ExpressionValid(e1)
        case ExpBinary(inst, e1, e2) => ExpressionValid(e1) && ExpressionValid(e2)
        case ExpIf(e1, e2, e3) => ExpressionValid(e1) && ExpressionValid(e2) && ExpressionValid(e3)
}

function ExpressionStackContainsOnlyWords(estack:seq<Expression>):bool
{
    forall i:int :: 0 <= i < |estack| ==> ExpressionValid(estack[i])
}

function EvaluateExpression(e:Expression, row:Row):int
    requires ExpressionValid(e);
    requires RowValid(row);
    ensures Word32(EvaluateExpression(e, row));
{
    match e
        case ExpInt(i) => i
        case ExpColumn(e1) => ExtractColumn(EvaluateExpression(e1, row), row)
        case ExpBinary(inst, e1, e2) => ApplyBinaryInstruction(inst, EvaluateExpression(e1, row), EvaluateExpression(e2, row))
        case ExpIf(e_cond, e_true, e_false) =>
            if EvaluateExpression(e_cond, row) != 0 then EvaluateExpression(e_true, row) else EvaluateExpression(e_false, row)
}

///////////////////////////////////////////
// Operations
///////////////////////////////////////////

function method ExtractColumn(column_index:int, row:Row):int
{
    if 0 <= column_index < |row.data| then row.data[column_index] else 0
}

datatype Operation = OperationPush(i:int)
                   | OperationColumn
                   | OperationBinary(inst:BinaryInstruction)
                   | OperationIf

function OperationValid(op:Operation):bool
{
    if op.OperationPush? then Word32(op.i) else true
}

function method StackSizeChangeFromOperation(t:Operation):int
{
    match t
        case OperationPush(_) => 1
        case OperationColumn => 0
        case OperationBinary(_) => -1
        case OperationIf => -2
}

///////////////////////////////////////////
// Programs
///////////////////////////////////////////

function ProgramContainsOnlyWords(program:seq<Operation>):bool
{
    forall k :: 0 <= k < |program| ==> OperationValid(program[k])
}

function StackSizeAfterRunning(program:seq<Operation>):int
{
    if |program| == 0 then 0
    else StackSizeAfterRunning(program[..|program| - 1]) + StackSizeChangeFromOperation(program[|program| - 1])
}

function ProgramPrefixValid(program:seq<Operation>):bool
{
    ProgramContainsOnlyWords(program) &&
    forall k :: 1 <= k <= |program| ==> StackSizeAfterRunning(program[..k]) >= 1
}

function ProgramValid(program:seq<Operation>):bool
{
    ProgramPrefixValid(program) && StackSizeAfterRunning(program) == 1
}

///////////////////////////////////////////
// Converting programs to expressions
///////////////////////////////////////////

function HowOperationChangesExpressionStack(op:Operation, estack:seq<Expression>):seq<Expression>
    requires |estack| + StackSizeChangeFromOperation(op) >= 1;
{
    match op
        case OperationPush(i) =>       estack + [ExpInt(i)]
        case OperationColumn =>        estack[..|estack|-1] + [ExpColumn(estack[|estack|-1])]
        case OperationBinary(inst) =>  estack[..|estack| - 2] + [ExpBinary(inst, estack[|estack| - 2], estack[|estack| - 1])]
        case OperationIf =>            estack[..|estack| - 3] + [ExpIf(estack[|estack|-3], estack[|estack| - 2], estack[|estack| - 1])]
}

function ProgramPrefixToExpressionStack(program:seq<Operation>):seq<Expression>
    requires ProgramPrefixValid(program);
    ensures |ProgramPrefixToExpressionStack(program)| == StackSizeAfterRunning(program);
    ensures ExpressionStackContainsOnlyWords(ProgramPrefixToExpressionStack(program));
{
    Lemma_PrefixesOfValidProgramPrefixesAreValid(program);
    assert program[..|program|] == program;
    assert |program| == 1 ==> StackSizeAfterRunning(program[..0]) + StackSizeChangeFromOperation(program[|program|-1]) >= 1;
    assert |program| > 1 ==> StackSizeAfterRunning(program[..|program|-1]) + StackSizeChangeFromOperation(program[|program|-1]) >= 1;
    if |program| == 0 then
        []
    else if |program| == 1 then
        HowOperationChangesExpressionStack(program[0], [])
    else
        HowOperationChangesExpressionStack(program[|program|-1], ProgramPrefixToExpressionStack(program[..|program|-1]))
}

function ProgramToExpression(program:seq<Operation>):Expression
    requires ProgramValid(program);
    ensures ExpressionValid(ProgramToExpression(program));
{
    ProgramPrefixToExpressionStack(program)[0]
}

function EvaluateProgram(program:seq<Operation>, row:Row):int
    requires ProgramValid(program);
    requires RowValid(row);
    ensures Word32(EvaluateProgram(program, row));
{
    EvaluateExpression(ProgramToExpression(program), row)
}

///////////////////////////////////////////
// Converting messages to programs
///////////////////////////////////////////

function method WordToOperation(w:int):Operation
    requires Word32(w);
{
       if w == 2000000001 then OperationColumn
    else if w == 2000000002 then OperationIf
    else if w == 2000000003 then OperationBinary(InstAdd)
    else if w == 2000000004 then OperationBinary(InstSub)
    else if w == 2000000005 then OperationBinary(InstMul)
    else if w == 2000000006 then OperationBinary(InstDiv)
    else if w == 2000000007 then OperationBinary(InstMod)
    else if w == 2000000008 then OperationBinary(InstGt)
    else if w == 2000000009 then OperationBinary(InstLt)
    else if w == 2000000010 then OperationBinary(InstEq)
    else if w == 2000000011 then OperationBinary(InstGe)
    else if w == 2000000012 then OperationBinary(InstLe)
    else OperationPush(w)
}

function MessageToProgram(message:seq<int>):seq<Operation>
    requires forall i :: 0 <= i < |message| ==> Word32(message[i]);
    ensures ProgramContainsOnlyWords(MessageToProgram(message));
{
    if |message| == 0 then [] else MessageToProgram(message[..|message|-1]) + [WordToOperation(message[|message|-1])]
}

/////////////////////////////////////////////////////////////////////////////////////////////
// Lemmas
/////////////////////////////////////////////////////////////////////////////////////////////

lemma Lemma_PrefixOfValidProgramPrefixIsValid(program:seq<Operation>, k:int)
    requires ProgramPrefixValid(program);
    requires 1 <= k <= |program|;
    ensures ProgramPrefixValid(program[..k]);
{
    var prefix := program[..k];
    assert forall i :: 1 <= i <= |prefix| ==> prefix[..i] == program[..i];
}

lemma Lemma_PrefixesOfValidProgramPrefixesAreValid(program:seq<Operation>)
    requires ProgramPrefixValid(program);
    ensures forall k :: 1 <= k <= |program| ==> ProgramPrefixValid(program[..k]);
{
    forall k:int | 1 <= k <= |program|
    {
        Lemma_PrefixOfValidProgramPrefixIsValid(program, k);
    }
}
