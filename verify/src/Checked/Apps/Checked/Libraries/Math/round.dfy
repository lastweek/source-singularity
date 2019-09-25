include "mul.dfy"
include "div.dfy"

method RoundUpToMultiple (x:nat, m:nat) returns (r:int)
    requires m > 0;
    ensures r % m == 0;
    ensures x <= r < x + m;
{

    lemma_div_pos_is_pos(x + m - 1, m);
    lemma_mod_multiples_basic(((x + m - 1) / m), m);
    r := ((x + m - 1) / m) * m;

    ghost var a := x / m;
    ghost var b := x % m;
    lemma_div_pos_is_pos(x, m);
    lemma_mul_positive(a, m);
    lemma_mul_is_commutative(a, m);
    lemma_fundamental_div_mod(x, m);
    lemma_mod_properties();
    assert x == m * a + b;

    if (b == 0) {
        calc {
            r;
            ((x + m - 1) / m) * m;
            ((m * a + m - 1) / m) * m;
            { lemma_fundamental_div_mod_converse_pos(m * a + m - 1, m, a, m - 1); }
            a * m;
            x;
        }
    }
    else {
        assert b > 0;
        lemma_mul_positive(m, a+1);
        lemma_mul_is_commutative(m, a+1);
        lemma_mul_is_mul_boogie(m, a+1);
        calc {
            r;
            ((x + m - 1) / m) * m;
            ((m * a + b + m - 1) / m) * m;
            (((m * a + m) + b - 1) / m) * m;
            (((m * a + m * 1) + b - 1) / m) * m;
            { lemma_mul_is_distributive_add(m, a, 1); lemma_mul_is_mul_boogie(m, a); lemma_mul_is_mul_boogie(m, a+1); }
            ((m * (a + 1) + b - 1) / m) * m;
            { lemma_fundamental_div_mod_converse_pos(m * (a+1) + b - 1, m, a + 1, b - 1); }
            (a + 1) * m;
            { lemma_mul_is_distributive_add(m, a, 1); lemma_mul_is_mul_boogie(m, a); lemma_mul_is_mul_boogie(m, a+1); }
            a * m + 1 * m;
            a * m + m;
        }
    }
}
