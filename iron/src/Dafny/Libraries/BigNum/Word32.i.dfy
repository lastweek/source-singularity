//-include "..\Util\assembly_deprecated.s.dfy"
include "..\Math\power2.i.dfy"

//-static function Word(w:nat, x:nat) : bool
//-{
//-    0 <= x < power2(w)
//-}

static function Width() : int
    ensures 0 < Width();
    { power2(32) }

//-static function Word32(x: nat): bool
//-    ensures Word32(x) <==> (x<Width());
//-{
//-    Word(32, x)
//-}

static lemma lemma_mul_is_mul_boogie_Width()
//-    ensures forall x:int::x * Width() == INTERNAL_mul_boogie(x, Width());
//-    ensures forall x:int::Width() * x == INTERNAL_mul_boogie(Width(), x);
{
//-    forall x:int
//-        ensures INTERNAL_mul(x, Width()) == INTERNAL_mul_boogie(x, Width());
//-        ensures INTERNAL_mul(Width(), x) == INTERNAL_mul_boogie(Width(), x);
//-    {
//-        lemma_mul_is_mul_boogie(x, Width());
//-        lemma_mul_is_mul_boogie(Width(), x);
//-    }
}

