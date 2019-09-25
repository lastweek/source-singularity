include "Libraries/Math/power2.dfy"
include "Libraries/Util/bytes_and_words.dfy"
include "Libraries/Util/arrays_and_seqs.dfy"

////////////////////////////////////////////////////////
// Functions with corresponding assembly instructions
////////////////////////////////////////////////////////

static function method {:axiom} AddInstruction(x: int, y: int) : int
    requires Word32(x);
    requires Word32(y);
    ensures Word32(AddInstruction(x, y));
    ensures AddInstruction(x, y) == (x + y) % power2(32);

static function method {:axiom} SubInstruction(x: int, y: int) : int
    requires Word32(x);
    requires Word32(y);
    ensures Word32(SubInstruction(x, y));
    ensures SubInstruction(x, y) == (x - y) % power2(32);

static function method {:axiom} MulInstruction(x: int, y: int) : int
    requires Word32(x);
    requires Word32(y);
    ensures Word32(MulInstruction(x, y));
    ensures MulInstruction(x, y) == (x * y) % power2(32);

static function method {:axiom} DivInstruction(x: int, y: int) : int
    requires Word32(x);
    requires Word32(y);
    requires y > 0;
    ensures Word32(DivInstruction(x, y));
    ensures DivInstruction(x, y) == (x / y) % power2(32);

static function method {:axiom} ModInstruction(x: int, y: int) : int
    requires Word32(x);
    requires Word32(y);
    requires y > 0;
    ensures Word32(ModInstruction(x, y));
    ensures ModInstruction(x, y) == x % y;

static function method {:axiom} LeftShiftInstruction(x: int, amount: int) : int
    requires Word32(x);
    requires 0 <= amount < 32;
    ensures Word32(LeftShiftInstruction(x, amount));
    ensures forall i {:trigger WordToSeq(LeftShiftInstruction(x, amount))[i]} :: 0 <= i < 32 - amount ==> WordToSeq(LeftShiftInstruction(x, amount))[i] == WordToSeq(x)[i+amount];
    ensures forall i {:trigger WordToSeq(LeftShiftInstruction(x, amount))[i]} :: 32 - amount <= i < 32 ==> WordToSeq(LeftShiftInstruction(x, amount))[i] == false;

static function method {:axiom} RightShiftInstruction(x: int, amount: int) : int
    requires Word32(x);
    requires 0 <= amount < 32;
    ensures Word32(RightShiftInstruction(x, amount));
    ensures forall i {:trigger WordToSeq(RightShiftInstruction(x, amount))[i]} :: 0 <= i < amount ==> WordToSeq(RightShiftInstruction(x, amount))[i] == false;
    ensures forall i {:trigger WordToSeq(RightShiftInstruction(x, amount))[i]} :: amount <= i < 32 ==> WordToSeq(RightShiftInstruction(x, amount))[i] ==  WordToSeq(x)[i-amount];

static function method {:axiom} RotateRightInstruction(x: int, amount: int) : int
    requires Word32(x);
    requires 0 <= amount < 32;
    ensures Word32(RotateRightInstruction(x, amount));
    ensures forall i {:trigger WordToSeq(RotateRightInstruction(x, amount))[i]} :: 0 <= i < amount ==> WordToSeq(RotateRightInstruction(x, amount))[i] == WordToSeq(x)[i+32-amount];
    ensures forall i {:trigger WordToSeq(RotateRightInstruction(x, amount))[i]} :: amount <= i < 32 ==> WordToSeq(RotateRightInstruction(x, amount))[i] ==  WordToSeq(x)[i-amount];

static function method {:axiom} RotateLeftInstruction(x: int, amount: int) : int
    requires Word32(x);
    requires 0 <= amount < 32;
    ensures Word32(RotateLeftInstruction(x, amount));
    ensures forall i {:trigger WordToSeq(RotateLeftInstruction(x, amount))[i]} :: 0 <= i < 32 - amount ==> WordToSeq(RotateLeftInstruction(x, amount))[i] == WordToSeq(x)[i+amount];
    ensures forall i {:trigger WordToSeq(RotateLeftInstruction(x, amount))[i]} :: 32 - amount <= i < 32 ==> WordToSeq(RotateLeftInstruction(x, amount))[i] ==  WordToSeq(x)[i+amount-32];

static function method {:axiom} BitwiseNotInstruction(x: int) : int
    requires Word32(x);
    ensures Word32(BitwiseNotInstruction(x));
    ensures forall i {:trigger WordToSeq(BitwiseNotInstruction(x))[i]} :: 0 <= i < 32 ==> WordToSeq(BitwiseNotInstruction(x))[i] == !WordToSeq(x)[i];

static function method {:axiom} BitwiseAndInstruction(x: int, y: int) : int
    requires Word32(x);
    requires Word32(y);
    ensures Word32(BitwiseAndInstruction(x, y));
    ensures forall i {:trigger WordToSeq(BitwiseAndInstruction(x, y))[i]} :: 0 <= i < 32 ==> WordToSeq(BitwiseAndInstruction(x, y))[i] == (WordToSeq(x)[i] && WordToSeq(y)[i]);

static function method {:axiom} BitwiseOrInstruction(x: int, y: int) : int
    requires Word32(x);
    requires Word32(y);
    ensures Word32(BitwiseOrInstruction(x, y));
    ensures forall i {:trigger WordToSeq(BitwiseOrInstruction(x, y))[i]} :: 0 <= i < 32 ==> WordToSeq(BitwiseOrInstruction(x, y))[i] == (WordToSeq(x)[i] || WordToSeq(y)[i]);

static function method {:axiom} BitwiseXorInstruction(x: int, y: int) : int
    requires Word32(x);
    requires Word32(y);
    ensures Word32(BitwiseXorInstruction(x, y));
    ensures forall i {:trigger WordToSeq(BitwiseXorInstruction(x, y))[i]} :: 0 <= i < 32 ==> WordToSeq(BitwiseXorInstruction(x, y))[i] == (WordToSeq(x)[i] != WordToSeq(y)[i]);
