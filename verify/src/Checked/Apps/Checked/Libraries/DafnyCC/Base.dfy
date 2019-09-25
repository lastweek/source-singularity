include "../../../Trusted/Spec/Libraries/Base.dfy"
static function{:imported} unroll_all(i:int):bool { true }
static function{:imported} INTERNAL_add_raw(x:int, y:int):int { x + y }
static function{:imported} INTERNAL_sub_raw(x:int, y:int):int { x + y }
type INTERNAL_AbsMem;
type INTERNAL_ArrayElems;
static function{:imported} INTERNAL_array_elems(a:array<int>):INTERNAL_ArrayElems
static function{:imported} INTERNAL_array_elems_index(a:INTERNAL_ArrayElems, k:int):int
static function{:imported} INTERNAL_array_elems_update(a:INTERNAL_ArrayElems, k:int, v:int):INTERNAL_ArrayElems
static function{:imported} INTERNAL_array_update(a:array<int>, k:int, v:int):INTERNAL_AbsMem

static method{:axiom} method_Mul(x:int, y:int) returns(r:int)
  ensures  r == x * y;
  ensures  r == INTERNAL_mul_boogie(x, y);

static method{:axiom} method_Div(x:int, y:int) returns(r:int)
  requires y != 0;
  ensures  r == x / y;
  ensures  r == INTERNAL_div_boogie(x, y);

static method{:axiom} method_Mod(x:int, y:int) returns(r:int)
  requires y != 0;
  ensures  r == x % y;
  ensures  r == INTERNAL_mod_boogie(x, y);

static method print_int(n:int)
{
}
