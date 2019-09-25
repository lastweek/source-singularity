static function Power2(exp: int) : int
    requires exp >= 0;
    ensures Power2(exp) > 0;
{
    if (exp==0) then
        1
    else
        2*Power2(exp-1)
}

static lemma Lemma_Power2Adds(e1:nat, e2:nat)
	ensures Power2(e1 + e2) == Power2(e1) * Power2(e2);
{
	if e2 == 0 {
		assert Power2(e2) == 1;	
	} else {
		var e2min1 := e2 - 1;
		calc {
			Power2(e1 + e2);
			Power2(e1 + e2 - 1) * 2;
			Power2(e1 + e2min1) * 2;
			{ Lemma_Power2Adds(e1, e2min1); }
			Power2(e1) * Power2(e2min1) * 2;
			Power2(e1) * Power2(e2-1) * 2;
			calc {
				Power2(e2);
				Power2(e2-1) * 2;
			}
			Power2(e1) * Power2(e2);
		}
		assert Power2(e1 + e2) == Power2(e1) * Power2(e2);
	}
}
