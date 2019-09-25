include "../../../Trusted/Spec/Apps/DiffPriv/Mapper_spec.dfy"

method DetermineIfProgramIsValid(program:seq<Operation>) returns (ret:bool)
    requires ProgramContainsOnlyWords(program);
    ensures ret == ProgramValid(program);
{
    var k := 0;
    var stack_size := 0;

    while k < |program|
        invariant 0 <= k <= |program|;
        invariant stack_size == StackSizeAfterRunning(program[..k]);
        invariant forall i :: 1 <= i <= k ==> StackSizeAfterRunning(program[..i]) >= 1;
    {
        stack_size := stack_size + StackSizeChangeFromOperation(program[k]);
        assert program[..k] + [program[k]] == program[..k+1];
        k := k + 1;
        assert StackSizeAfterRunning(program[..k]) == stack_size;
        if stack_size < 1
        {
            return false;
        }
    }

    assert program[..k] == program;
    return stack_size == 1;
}

method ConvertMessageToProgram(message:seq<int>) returns (ret:seq<Operation>)
    requires forall i :: 0 <= i < |message| ==> Word32(message[i]);
    ensures ret == MessageToProgram(message);
{
    var i := 0;
    ret := [];

    while i < |message|
        invariant 0 <= i <= |message|;
        invariant ret == MessageToProgram(message[..i]);
    {
        ret := ret + [WordToOperation(message[i])];
        assert message[..i] + [message[i]] == message[..i+1];
        i := i + 1;
    }

    assert message[..i] == message;
}

method {:timeLimit 30} RunProgram(program:seq<Operation>, row:Row) returns(ret:int)
    requires ProgramValid(program);
    requires RowValid(row);
    ensures ret == EvaluateExpression(ProgramToExpression(program), row);
    ensures Word32(ret);
{
    var stack:seq<int> := [];
    var k:int := 0;

    ghost var estack:seq<Expression> := [];

    Lemma_PrefixesOfValidProgramPrefixesAreValid(program);

    while (k < |program|)
        invariant 0 <= k <= |program|;
        invariant |stack| == StackSizeAfterRunning(program[..k]);
        invariant estack == ProgramPrefixToExpressionStack(program[..k]);
        invariant forall i :: 0 <= i < |stack| ==> stack[i] == EvaluateExpression(estack[i], row);
    {
        assert program[..k+1] == program[..k] + [program[k]];

        match program[k]
        {
            case OperationPush(i) =>
                estack := estack + [ExpInt(i)];
                stack := stack + [i];

            case OperationColumn =>
                estack := estack[..|estack|-1] + [ExpColumn(estack[|estack|-1])];
                stack := stack[..|stack|-1] + [ExtractColumn(stack[|stack|-1], row)];

            case OperationBinary(inst) =>
                estack := estack[..|estack| - 2] + [ExpBinary(inst, estack[|estack| - 2], estack[|estack| - 1])];
                stack := stack[..|stack| - 2] + [ApplyBinaryInstruction(inst, stack[|stack| - 2], stack[|stack| - 1])];

            case OperationIf =>
                estack := estack[..|estack| - 3] + [ExpIf(estack[|estack|-3], estack[|estack| - 2], estack[|estack| - 1])];
                stack := stack[..|stack| - 3] + [if stack[|stack|-3] != 0 then stack[|stack| - 2] else stack[|stack| - 1]];
        }

        k := k + 1;
    }

    assert program == program[..|program|];
    assert |stack| == 1;
    ret := stack[0];
}
