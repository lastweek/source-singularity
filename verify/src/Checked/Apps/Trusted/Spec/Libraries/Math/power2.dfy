include "../Base.dfy"

static function {:hidden} power2(exp: nat) : nat 
    ensures power2(exp) > 0;
{
    if (exp==0) then
        1
    else
        2*power2(exp-1)
}

static lemma lemma_power2_32()
    ensures power2(8) == 0x100;
    ensures power2(16) == 0x10000;
    ensures power2(24) == 0x1000000;
    ensures power2(32) == 0x100000000;
{
    reveal_power2();
    assert unroll(1) && unroll(2) && unroll(3) && unroll(4) && unroll(5) && unroll(6) && unroll(7) && unroll(8);
}
