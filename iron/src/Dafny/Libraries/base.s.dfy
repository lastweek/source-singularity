static function{:imported} unroll(i:int):bool { true }
static function Trigger(i:int):bool { true }
static function sizeof<A>(a:A):int

//-static function{:axiom} mod0x100000000(x:int):int
//-static lemma{:axiom} lemma_mod0x100000000(x:int)
//-    ensures mod0x100000000(x) == x % 0x100000000;

//-static method{:axiom} method_Mul(x:int, y:int) returns(r:int)
//-    ensures  r == x * y;
//-    ensures  r == INTERNAL_mul_boogie(x, y);
//-
//-static method{:axiom} method_Div(x:int, y:int) returns(r:int)
//-    requires y != 0;
//-    ensures  r == x / y;
//-    ensures  r == INTERNAL_div_boogie(x, y);
//-
//-static method{:axiom} method_Mod(x:int, y:int) returns(r:int)
//-    requires y != 0;
//-    ensures  r == x % y;
//-    ensures  r == INTERNAL_mod_boogie(x, y);
