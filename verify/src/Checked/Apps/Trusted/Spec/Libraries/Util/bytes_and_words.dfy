include "../Math/power2.dfy"

static predicate IsBit(b:int)
{
	0 <= b < 2
}

static predicate IsByte(b:int)
{
	0 <= b < 256
}

static predicate IsWord(w: int)
{
    0 <= w < power2(32)
}

//
// TODO deprecate and delete old terminology
//

static predicate Word32(x: int) { IsWord(x) }
