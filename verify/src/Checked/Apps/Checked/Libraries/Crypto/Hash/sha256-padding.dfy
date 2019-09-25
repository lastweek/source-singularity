/////////////////////////////////////////////////////
// Power2
/////////////////////////////////////////////////////

static function method Power2(exp: nat): nat
	requires exp>=0;
	ensures Power2(exp) > 0;
	ensures exp>0 ==> Power2(exp) == 2*Power2(exp-1);
{
	if (exp==0) then
		1
	else
		2*Power2(exp-1)
}

static predicate Lemma_TwoToTheThirtyTwoIs()
	ensures 4294967296 == Power2(32);
	ensures Lemma_TwoToTheThirtyTwoIs();
{
	assert(512 == Power2(9));
	assert(262144 == Power2(18));
	assert(268435456 == Power2(28));
	true
}

static predicate Lemma_Power2TurnsAdditionIntoMultiplication(e1:nat, e2:nat)
	ensures Power2(e1+e2) == Power2(e1) * Power2(e2);
	ensures Lemma_Power2TurnsAdditionIntoMultiplication(e1, e2);
{
	if e2 == 0 then
		true
	else
		Lemma_Power2TurnsAdditionIntoMultiplication(e1, e2-1)
}

static predicate Lemma_Power2IsIncreasing(e1:nat, e2:nat)
	requires e1 <= e2;
	ensures Power2(e1) <= Power2(e2);
	ensures Lemma_Power2IsIncreasing(e1, e2);
	decreases e2;
{
	if e2 == e1 then
		true
	else
		Lemma_Power2IsIncreasing(e1, e2-1)
}

/////////////////////////////////////////////////////
// Basic instructions
/////////////////////////////////////////////////////

static function method not (x:int):int
static function method and (x:int, y:int):int
static function method or  (x:int, y:int):int
static function method xor (x:int, y:int):int
static function method add (x:int, y:int):int
static function method sub (x:int, y:int):int
static function method right_shift (x:int, amt:int):int
static function method left_shift  (x:int, amt:int):int

static function method word(x:int):bool
{
	0 <= x < Power2(32)
}

// Assumed in Dafny, proven in Boogie (someday)
ghost method lemma_word()
	ensures (forall x:int :: word(x) ==> word(not(x)));
	ensures (forall x:int, y:int :: word(x) && word(y) ==> word(and(x, y)));
	ensures (forall x:int, y:int :: word(x) && word(y) ==> word(or (x, y)));
	ensures (forall x:int, y:int :: word(x) && word(y) ==> word(xor(x, y)));
	ensures (forall x:int, y:int :: word(x) && word(y) ==> word(add(x, y)));
	ensures (forall x:int, y:int :: word(x) && word(y) ==> word(sub(x, y)));
	ensures (forall x:int, amt:int :: word(x) && 0 <= amt <= 32 ==> word(right_shift(x, amt)));
	ensures (forall x:int, amt:int :: word(x) && 0 <= amt <= 32 ==> word(left_shift (x, amt)));

// Assumed in Dafny, proven in Boogie (someday)
ghost method lemma_bit_masks()
	requires (forall x:int :: word(x) ==> word(not(x)));
	requires (forall x:int, y:int :: word(x) && word(y) ==> word(and(x, y)));
	requires (forall x:int, y:int :: word(x) && word(y) ==> word(sub(x, y)));	
	requires (forall x:int, amt:int :: word(x) && 0 <= amt <= 32 ==> word(left_shift (x, amt)));
	ensures (forall x:int, amt:int, index:int :: word(x) && bit_index(amt) && bit_index(index) ==> 
				get_bit(index, and(x, not(sub(left_shift(1, amt), 1)))) ==
				if index < amt then 0 else get_bit(index, x)  );
	ensures forall index:int :: bit_index(index) ==> get_bit(index, 0) == 0;


function RightShift32(x:nat, amount:nat) : nat
	requires amount <= 32;
	requires word(x);
	ensures RightShift32(x, amount) <= x;
	ensures word(RightShift32(x, amount));
	decreases amount;
{
	if amount == 0 then
		x
	else
		//RightShift(w, x/2, amount-1)
		RightShift32(int_div(x, 2), amount-1)
}

// Assumed in Dafny, proven in Boogie (someday)
ghost method lemma_equivalences()
	/*
	ensures (forall x:int :: word(x) ==> not(x) == BitwiseNOT32(x));
	ensures (forall x:int, y:int :: word(x) && word(y) ==> and(x, y) == BitwiseAND32(x, y));
	ensures (forall x:int, y:int :: word(x) && word(y) ==> or (x, y) == BitwiseOR32(x, y));
	ensures (forall x:int, y:int :: word(x) && word(y) ==> xor(x, y) == BitwiseXOR32(x, y));
	ensures (forall x:int, y:int :: word(x) && word(y) ==> add(x, y) == MakeWord(32, x + y));
	//ensures (forall x:int, y:int :: word(x) && word(y) ==> sub(x, y) == MakeWord(32, x - y));
	*/
	ensures (forall x:int, amt:int :: word(x) && 0 <= amt <= 32 ==> right_shift(x, amt) == RightShift32(x, amt));
	//ensures (forall x:int, amt:int :: word(x) && 0 <= amt <= 32 ==> left_shift (x, amt) ==  LeftShift32(x, amt));


/////////////////////////////////////////////////////
// Dafny/z3-friendly division
/////////////////////////////////////////////////////


function int_div(x:int, y:int) : int
	requires x >= 0;
	requires y >  0;
	ensures 0 <= int_div(x, y) <= x;
{
	if (x - y < 0) then 0
	else int_div(x - y, y) + 1
}

ghost method lemma_div_is_ordered(x:int, y:int, z:int)
	requires 0 <= x <= y;
	requires z > 0;
	ensures int_div(x, z) <= int_div(y, z);
{
}

ghost method lemma_even_div(d:int) 
	requires d >= 0;
	requires d % 2 == 0;
	ensures 2 * int_div(d, 2) == d;
{
	var k := int_div(d, 2);
	var r := d -  k * 2;
	lemma_remainder(d, 2);		
	assert r == 0;
	calc {
		2 * int_div(d, 2);
		2 * int_div(2*k, 2);
		{ lemma_div_by_multiple_simple(k, 2); }
		2 * k;
		d;
	}
}

ghost method lemma_odd_div(d:int) 
	requires d >= 0;
	requires d % 2 == 1;
	ensures 2 * int_div(d, 2) + 1 == d;
{
}

ghost method lemma_pow2_div(a:int, b:int) 
	requires a >= 0;
	requires b >= 0;
	ensures int_div(a, Power2(b + 1)) == int_div(int_div(a, Power2(b)), 2);
{
	calc {
		int_div(a, Power2(b + 1));
		{ assert Lemma_Power2TurnsAdditionIntoMultiplication(b, 1); }
		int_div(a, Power2(b) * 2);
		//{ lemma_repeated_div_simple(a, Power2(b), 2); }
		{ lemma_repeated_div(a, Power2(b), 2, Power2(b) * 2); }
		int_div(int_div(a, Power2(b)), 2);
	}
}


ghost method lemma_right_shift_is_div_pow2(x:int, amt:int) 
	requires word(x) && bit_index(amt);
	ensures RightShift32(x, amt) == int_div(x, Power2(amt));
{
	if (amt == 0) {
	} else {
		calc {
			RightShift32(x, amt);
			RightShift32(int_div(x, 2), amt-1);
			int_div(int_div(x, 2), Power2(amt-1));
			{ lemma_repeated_div_simple(x, 2, Power2(amt-1)); }
			int_div(x, 2*Power2(amt-1));
			int_div(x, Power2(amt));
		}			
	}		
}
	

ghost method lemma_div_by_multiple_is_strongly_ordered(x:int, y:int, m:int, z:int)
	requires 0 < m;
	requires 0 <= x < y;
	requires y == m * z;
	requires z > 0;	
	ensures	 int_div(x, z) < int_div(y, z);
{
	lemma_div_by_multiple_simple(m, z);
	assert(int_div(y, z) == m);

	var k := int_div(x, z);
	var r := x - int_div(x, z) * z;
	lemma_remainder(x, z);
	assert 0 <= r < z;

	assert k*z <= k*z + r < m*z;
	lemma_div_by_multiple_simple(k, z);
	assert int_div(k*z, z) == k;

}

ghost method lemma_remainder(x:int, divisor:int)
	requires 0 <= x;
	requires 0 < divisor;
	ensures  0 <= x - int_div(x, divisor) * divisor < divisor;
{		
}


ghost method lemma_div_mod(a:int, b:int)
	requires 0 <= a;
	requires 0 < b;
	requires a % b == 0;	
	ensures  b * int_div(a, b) == a;		
{
	var k := a / b;
	assert a == mul_wrapper(k, b);
	calc {
		b * int_div(a, b);
		mul_wrapper(b, int_div(a, b));
		{ lemma_div_by_multiple_simple(k, b); }
		mul_wrapper(b, k);
		b * k;
		a;
	}
	
}
	
function mul_wrapper(a:int, b:int):int
{
	a * b
}


ghost method lemma_div_by_multiple_simple(a:int, b:int)
	requires 0 <= a;
	requires 0 < b;
	ensures  int_div(a*b, b) == a;		
{
	lemma_div_by_multiple(a*b, a, b);
}
		
ghost method lemma_div_by_multiple(bd:int, b:int, d:int)
	requires 0 <= bd && 0 <= b;
	requires bd == b * d;
	requires 0 < d;
	ensures  int_div(bd, d) == b;	
	decreases bd;	
{
	if (bd*d - d < 0) {
		assert bd == 0;
		assert int_div(bd, d) == 0;
	} else {
		lemma_div_by_multiple(bd - d, b - 1, d);
	}
}

ghost method lemma_repeated_div_simple(x:int, y:int, z:int)
	requires 0 <= x;
	requires 0 < y && 0 < z;
	ensures int_div(int_div(x, y), z) == int_div(x, y*z);
{
	lemma_repeated_div(x, y, z, y*z);
}

ghost method lemma_repeated_div(x:int, y:int, z:int, yz:int)
	requires 0 <= x;
	requires 0 < y && 0 < z;
	requires yz == y * z;
	ensures int_div(int_div(x, y), z) == int_div(x, yz);
{
	lemma_repeated_div_lower_bound(x, y, z, yz);
	lemma_repeated_div_upper_bound(x, y, z, yz);
}

ghost method lemma_repeated_div_lower_bound(x:int, y:int, z:int, yz:int)
	requires 0 <= x;
	requires 0 < y && 0 < z;
	requires yz == y * z;
	ensures int_div(int_div(x, y), z) <= int_div(x, yz);
{
	var k := int_div(x, y);
	var r := x - int_div(x, y) * y;
	lemma_remainder(x, y);
	assert 0 <= r < y;

	var a := int_div(k, z);
	var b := k - int_div(k, z) * z;
	lemma_remainder(k, z);		

	assert x == a * yz + b * y + r;
	
	lemma_div_by_multiple_simple(a, yz);
	assert int_div(a*yz, yz) == a;
	assert a*yz <= x;		
		
	lemma_div_is_ordered(a*yz, x, yz);
	assert int_div(a*yz, yz) <= int_div(x, yz);

	assert a <= int_div(x, yz);	// Lower-bound
	assert int_div(int_div(x, y), z) <= int_div(x, yz);
	assert int_div(int_div(x, y), z) <= int_div(x, y*z);
}


ghost method lemma_repeated_div_upper_bound(x:int, y:int, z:int, yz:int)
	requires 0 <= x;
	requires 0 < y && 0 < z;
	requires yz == y * z;
	ensures  int_div(x, yz) <= int_div(int_div(x, y), z); 
{
	var k := int_div(x, y);
	var r := x - int_div(x, y) * y;
	lemma_remainder(x, y);
	assert 0 <= r < y;

	var a := int_div(k, z);
	var b := k - int_div(k, z) * z;
	lemma_remainder(k, z);
	assert 0 <= b < z;
		
	assert int_div(int_div(x, y), z) == a;
	assert x == k * y + r;
	assert k == a * z + b;
	assert x == a * yz + b * y + r;

	var c := b + 1;
	var d := a + 1;

	calc ==> {
		true;
		c <= z; 
		y*c <= y*z;
		y*(b+1) <= yz;
		y*b + y <= yz;
		y*b + r < y*b + y <= yz;
		y*b + r < yz;
		a * yz +  y*b + r < a * yz + yz;
		x < (a+1) * yz;
		x < d * yz;
		{ lemma_div_by_multiple_is_strongly_ordered(x, d * yz, d, yz); }
		int_div(x, yz) < int_div(d * yz, yz);
		calc == {
			int_div(d * yz, yz);
			{ lemma_div_by_multiple_simple(d, yz); }
			d;
		}
		int_div(x, yz) < d;
		int_div(x, yz) <= d - 1;
		int_div(x, yz) <= a;
		int_div(x, yz) <= int_div(int_div(x, y), z);
	}
		
	assert int_div(x, yz) <= int_div(int_div(x, y), z);		
}
		
function sub2(x:int, y:int) : int
{
	x - y
}


/////////////////////////////////////////////////////
// Operations on arrays and sequences
/////////////////////////////////////////////////////

static function bit_index(amt:int):bool
{
	0 <= amt < 32
}

// The biggest problem child
static function seq_to_int(data:seq<int>, len:int) : int
	requires 0 <= len <= |data| * 32;	
	requires len < Power2(32);
	requires forall i :: 0 <= i < |data| ==> word(data[i]);		
	ensures seq_to_int(data, len) >= 0;
	ensures  len > 0 ==> seq_to_int(data, len) >= seq_to_int(data, len-1);
	ensures  (len > 0 && get_seq_bit(0, data, len) == 1) ==> (seq_to_int(data, len) == 2 * seq_to_int(data, len - 1) + 1);
	ensures  (len > 0 && get_seq_bit(0, data, len) == 0) ==> (seq_to_int(data, len) == 2 * seq_to_int(data, len - 1));
	ensures  (len > 0 && get_seq_bit(0, data, len) == 0) ==> (seq_to_int(data, len) == Power2(1) * seq_to_int(data, len - 1));
	ensures  seq_to_int(data, 0) == 0;
// Try hiding the body to see if it improves proof time of other methods
{	
	if len <= 0 then 0
	else 
		2 * seq_to_int(data, len - 1) + get_seq_bit(0, data, len)
}


// Write out the array, with arr[0] as the most-significant int, and arr[len-1] the least-signifcant int
// Each int is itself in big-endian order.  The bits are numbered from 0, starting at the least-signficant (i.e., the rightmost of the len bits)
// Len is the total number of bits to consider
static function get_array_bit(bit_index:int, arr:array<int>, len:int) : int
	reads arr;	
	requires arr != null && 0 <= bit_index < len;
	requires len <= arr.Length * 32;
	requires word(arr[(len - bit_index - 1) / 32]);
{
	var index := len - bit_index - 1;		// Convert into a bit index counting from the "left" or MSB position
	var inter_int_index := index / 32;
	var intra_int_index := 31 - index % 32;	// Convert back into an index from the "right" or LSB for indexing within the int
	get_bit(intra_int_index, arr[inter_int_index])
}

static function get_seq_bit(bit_index:int, data:seq<int>, len:int) : int		
	requires 0 <= bit_index < len;
	requires len <= |data| * 32;
	requires word(data[(len - bit_index - 1) / 32]);
{
	var index := len - bit_index - 1;		// Convert into a bit index counting from the "left" or MSB position
	var inter_int_index := index / 32;
	var intra_int_index := 31 - index % 32;	// Convert back into an index from the "right" or LSB for indexing within the int
	get_bit(intra_int_index, data[inter_int_index])
}

	
// Bits are indexed from 0, starting with the least-signficant (i.e., the rightmost)
static function get_bit(bit_index:int, my_int:int) : int
	requires word(my_int);
	requires 0 <= bit_index < 32;
{	
	right_shift(my_int, bit_index) % 2
}


static function set_array_bit(bit_index:int, arr:seq<int>, len:int) : seq<int>
	requires 0 <= bit_index < len;
	requires len <= |arr| * 32;
	requires word(arr[(len - bit_index - 1) / 32]);
{
	var index := len - bit_index - 1;		// Convert into a bit index counting from the "left" or MSB position
	var inter_int_index := index / 32;
	var intra_int_index := 31 - index % 32;	// Convert back into an index from the "right" or LSB for indexing within the int
	arr[inter_int_index := set_bit(intra_int_index, arr[inter_int_index])]
}

// Bits are indexed from 0, starting with the least-signficant (i.e., the rightmost)
static function method set_bit(bit_index:int, my_int:int) : int
	requires word(my_int);
	requires 0 <= bit_index < 32;
{	
	or(my_int, left_shift(1, bit_index))
}

//////////////////////////////////////////////////////////
// Basic lemmas about operations on arrays and sequences
//////////////////////////////////////////////////////////

ghost method lemma_get_array_bit_consistent(d1:array<int>, d2:array<int>, num_matches:int)
	requires d1 != null && d2 != null;
	requires 0 <= num_matches && num_matches < d1.Length && num_matches < d2.Length;
	requires forall index:int :: 0 <= index < num_matches ==> d1[index] == d2[index];
	requires forall index:int :: 0 <= index < d1.Length ==> word(d1[index]);
	requires forall index:int :: 0 <= index < d2.Length ==> word(d2[index]);
	ensures  forall i:int :: 0 <= i < num_matches * 32 ==> get_array_bit(i, d1, num_matches*32) == get_array_bit(i, d2, num_matches*32);
{
	//true
}

ghost method lemma_get_array_seq_bit_consistent(d1:array<int>, d2:seq<int>, num_matches:int)
	requires d1 != null;
	requires 0 <= num_matches && num_matches < d1.Length && num_matches < |d2|;
	requires forall index:int :: 0 <= index < num_matches ==> d1[index] == d2[index];
	requires forall index:int :: 0 <= index < d1.Length ==> word(d1[index]);
	requires forall index:int :: 0 <= index < |d2| ==> word(d2[index]);
	ensures  forall i:int :: 0 <= i < num_matches * 32 ==> get_array_bit(i, d1, num_matches*32) == get_seq_bit(i, d2, num_matches*32);
{
	//true
}

ghost method lemma_bit_get_set() 
	ensures forall x:int, index:int :: word(x) && 0 <= index < 32 ==> word(set_bit(index, x));
	ensures forall x:int, index:int :: word(x) && 0 <= index < 32 ==> get_bit(index, set_bit(index, x)) == 1;

/////////////////////////////////////////////////////
// Padding
/////////////////////////////////////////////////////

// The actual spec
static function Pad(len:nat, m:nat) : nat
	requires len < Power2(64);
	requires m < Power2(len);
{
	m * Power2(1 + NumPaddingZeroes(len) + 64) + Power2(NumPaddingZeroes(len) + 64) + len
}

static function NumPaddingZeroes(len: nat) : nat
	requires len < Power2(64);
	ensures (len + 1 + NumPaddingZeroes(len) + 64) % 512 == 0;
	ensures forall j : nat :: j < NumPaddingZeroes(len) ==> (len + 1 + j + 64) % 512 != 0;
	ensures NumPaddingZeroes(len) < 512;
{
	(959 - (len % 512)) % 512
}

static function PaddedLength(len:nat) : nat
	requires len < Power2(64);
	ensures PaddedLength(len) % 512 == 0;
{
	len + 1 + NumPaddingZeroes(len) + 64
}

// Restated to be more implementation friendly (outside the TCB)
static function method min_padded_len(msg_len:int) : int
{
	msg_len + 1 + 64	// Add 1 bit for the 1 and 64 for the length field
}

static function method num_padding_zeroes(msg_len:int) : int
{
	(512 - (min_padded_len(msg_len) % 512)) % 512
}

// This function always teeters between provable and time-outs.  Also struggles with well-formedness.
static function method {:timeLimit 40} padded_len(msg_len:int) : int
	requires word(msg_len);
	requires msg_len <= Power2(32) - 1;
	requires Lemma_Power2IsIncreasing(32, 64);
	ensures  padded_len(msg_len) % 512 == 0;
	ensures  padded_len(msg_len) == PaddedLength(msg_len);
{
	assert(Lemma_Power2IsIncreasing(32, 64));
	min_padded_len(msg_len) + num_padding_zeroes(msg_len)
}



/////////////////////////////////////////////////////
// Implementation
/////////////////////////////////////////////////////

// The following verifies successfully.  Body commented out to speed proofs
method padding_complete(data: array<int>, len: int) 
	requires word(len);
	requires len <= Power2(32) - 1 && len < Power2(64);
	requires data != null;	
	requires data.Length * 32 == len;
	requires data.Length * 32 > padded_len(len);		// Make padding easier
	requires padded_len(len) < Power2(32);	
	requires forall i :: 0 <= i < data.Length ==> word(data[i]);
	requires seq_to_int(data[..], len) < Power2(len);
	requires padded_len(len) == PaddedLength(len);
	modifies data;
	ensures  forall i :: 0 <= i < data.Length ==> word(data[i]);
	ensures  seq_to_int(data[..], PaddedLength(len)) == Pad(len, old(seq_to_int(data[..], len)));	
{
	pad_message_with_zeroes(data, len);
	assert old(seq_to_int(data[..], len)) == seq_to_int(data[..], len);
	ghost var padding := NumPaddingZeroes(len) + 64;
	lemma_pad_message(data, len, padding);

	/*
	assert seq_to_int(data[..], PaddedLength(len)) == Power2(32) * seq_to_int(data[..], PaddedLength(len) - 32);
	assert seq_to_int(data[..], PaddedLength(len)) == Power2(1 + padding) * seq_to_int(data[..], len) + Power2(padding);
	assert Power2(32) * seq_to_int(data[..], PaddedLength(len) - 32) == Power2(1 + padding) * seq_to_int(data[..], len) + Power2(padding);
	*/
	ghost var a2i_minus32 := seq_to_int(data[..], PaddedLength(len) - 32);

	padding_add_len(data, len);

	calc {
		seq_to_int(data[..], PaddedLength(len));
		seq_to_int(data[..], PaddedLength(len) - 32) * Power2(32) + len;
		a2i_minus32 * Power2(32) + len; 
		Power2(1 + padding) * seq_to_int(data[..], len) + Power2(padding) + len;
		//seq_to_int(data, len) * Power2(1 + padding) + Power2(padding) + len;
		seq_to_int(data[..], len) * Power2(1 + NumPaddingZeroes(len) + 64) + Power2(NumPaddingZeroes(len) + 64) + len; 
		Pad(len, seq_to_int(data[..], len));
		calc {
			old(seq_to_int(data[..], len));
			seq_to_int(data[..], len);
		}		
		Pad(len, old(seq_to_int(data[..], len)));  
	}
	//assert(	seq_to_int(data, PaddedLength(len)) == Pad(len, old(seq_to_int(data, len))) );
}

	

// The following verifies successfully.  Body commented out to speed proofs
method {:timeLimit 30}pad_message_with_zeroes(data: array<int>, len: int)
	requires word(len);
	requires len <= Power2(32) - 1 && len < Power2(64);
	requires data != null;	
	requires data.Length * 32 >= len;
	requires data.Length * 32 > padded_len(len);		// Make padding easier
	requires padded_len(len) < Power2(32);	
	requires forall i :: 0 <= i < data.Length ==> word(data[i]);
	requires seq_to_int(data[..], len) < Power2(len);
	//requires array2int(data, 0) < Power2(len);
	modifies data;
	ensures  forall i :: 0 <= i < data.Length ==> word(data[i]);
	ensures  forall bit_index :: 0 <= bit_index < NumPaddingZeroes(len) + 64 ==> get_array_bit(bit_index, data, PaddedLength(len)) == 0;
	ensures  seq_to_int(data[..], len + 1) == 2*seq_to_int(data[..], len) + 1;
	ensures  seq_to_int(data[..], len) < Power2(len);
	ensures  old(seq_to_int(data[..], len)) == seq_to_int(data[..], len);	// We don't change the original data	
	{
	//assert(0 <= array2int(data, 0) < Power2(len));
	lemma_word();

	// Apply padding
	var one_bit_index := len / 32;
	data[one_bit_index] := set_bit(31 - (len % 32), data[one_bit_index]);   // Add the final 1
	lemma_bit_get_set();
	assert(get_bit(31 - (len % 32), set_bit(31 - (len % 32), old(data[one_bit_index]))) == 1);
	assert(get_bit(31 - (len % 32), data[one_bit_index]) == 1);
	assert(get_array_bit(0, data, len+1) == get_bit(31 - (len % 32), data[len/32]));
	assert(get_array_bit(0, data, len+1) == 1);
	assert(seq_to_int(data[..], len + 1) == 2*seq_to_int(data[..], len) + 1);
	assert(data[..] == old(set_array_bit(0, data[..], len+1)));

	ghost var num_zeroes := 0;
	ghost var d := data[one_bit_index];
	data[one_bit_index] := and(data[one_bit_index], not(sub(left_shift(1, 31 - (len % 32)), 1)));	// Set remaining LSB bits of this int to 0
	lemma_bit_masks();
	
	ghost var amt := 31 - (len % 32);
	ghost var result := data[one_bit_index]; 
	assert(result == and(d, not(sub(left_shift(1, amt), 1))));
	assert(forall index:int :: bit_index(index) && index < amt ==> get_bit(index, result) == 0);

	assert(forall index:int :: bit_index(index) && index < amt ==> get_bit(index, data[one_bit_index]) == 0);
	assert(forall index:int :: bit_index(index) && index >= amt ==> get_bit(index, data[one_bit_index]) == get_bit(index, d));


	// Correct, but a nuisance
	//num_zeroes := num_zeroes + (32 - ((len + 1)%32)) % 32;
	num_zeroes := 31 - (len % 32);
	assert(one_bit_index * 32 <= len <= data.Length * 32);
	assert(one_bit_index * 32 < padded_len(len));	
	assert(0 <= num_zeroes < 32);
	
	//assert(forall x:int :: x > 0 ==> (32 - ((x + 1)%32)) % 32 == (-1*(x+1))%32);
	assert(forall index:int :: bit_index(index) && index < num_zeroes ==> get_bit(index, data[one_bit_index]) == 0);
		
	//assert(len % 32 < 31 ==> len/32 == (len+1)/32);

	assert(forall i :: 0 <= i < num_zeroes ==> get_array_bit(i, data, len+1+num_zeroes) == 0); 
	
	assert (len + 1 + num_zeroes) % 32 == 0; 
	assert (len + 1 + num_zeroes) / 32 == one_bit_index + 1;
	data[one_bit_index + 1] := 0;
	assert(forall i :: 0 <= i < num_zeroes+32 ==> get_array_bit(i, data, len+1+num_zeroes+32) == 0); 
	data[one_bit_index + 2] := 0;
	assert(forall i :: 0 <= i < num_zeroes+32+32 ==> get_array_bit(i, data, len+1+num_zeroes+32+32) == 0); 

	// Pad with 0s
	var index := one_bit_index + 1;
	//ghost var old_num_zeroes := num_zeroes;
	ghost var old_data := data[0..index];

	//assert(forall i :: 0 <= i < old_num_zeroes ==> get_array_bit(i, data, len+1+old_num_zeroes) == 0);
	lemma_mod_512_is_mod_32(padded_len(len));
	while ( index * 32 < padded_len(len) )		// Use a forall here
		invariant forall i :: 0 <= i < data.Length ==> word(data[i]);
		invariant index * 32 <= padded_len(len);
		invariant forall i :: one_bit_index + 1 <= i < index ==> data[i] == 0;
		invariant forall i :: 0 <= i <= one_bit_index ==> data[i] == old_data[i];
	{
		data[index] := 0;
		index := index + 1;
	}

	// Prove that we've set all the approprate bits to zero
	assert(forall i :: 0 <= i < num_zeroes ==> get_array_bit(i, data, len+1+num_zeroes) == 0); 
	assert forall i :: one_bit_index + 1 <= i < padded_len(len) / 32 ==> data[i] == 0;
	assert get_array_bit(0, data, padded_len(len)) == 0;
	ghost var num_zero_ints := int_div(padded_len(len), 32) - (one_bit_index + 1);
	lemma_mod_512_is_mod_32(padded_len(len));
	calc {
		num_zero_ints * 32;
		32*int_div(padded_len(len), 32) - 32*(one_bit_index + 1);
		{ lemma_div_mod(padded_len(len), 32); }
		padded_len(len)- 32*(one_bit_index + 1);
	}
	assert forall bit_index :: 0 <= bit_index < num_zero_ints * 32 ==> get_array_bit(bit_index, data, padded_len(len)) == 0;
	assert forall bit_index :: 0 <= bit_index < num_zero_ints * 32 + num_zeroes ==> get_array_bit(bit_index, data, padded_len(len)) == 0;

	ghost var num_padding_0s := num_zero_ints * 32 + num_zeroes - 64;
	//assert NumPaddingZeroes(len) == num_padding_zeroes(len);
	calc {
		num_padding_0s;
		num_zero_ints * 32 + num_zeroes - 64;
		//32*(padded_len(len) / 32 - (one_bit_index + 1)) + 31 - (len % 32) - 64;
		//32* (padded_len(len) / 32) - 32 * (one_bit_index + 1) + 31 - (len % 32) - 64;
		32* int_div(padded_len(len), 32) - 32 * (one_bit_index + 1) + 31 - (len % 32) - 64;
		padded_len(len) - 32 * (len / 32 + 1) + 31 - (len % 32) - 64;
		padded_len(len) - 32 * (len / 32 + 1) - (len % 32) - 33;
	}
	if (len % 32 == 0) {
		calc {
			num_padding_0s;
			padded_len(len) - 32 * (len / 32 + 1) - (len % 32) - 33;
			padded_len(len) - (len + 32) - 0 - 33;
			padded_len(len) - len - 1 - 64;
			padded_len(len) - (len + 1 + 64);
		}
	} else {
		calc {
			num_padding_0s;
			padded_len(len) - 32 * (len / 32 + 1) - (len % 32) - 33;
			padded_len(len) - (len - len % 32 + 32) - (len % 32) - 33;
			padded_len(len) - len - 32 - 33;
			padded_len(len) - (len + 64 + 1);
		}
	}
	assert num_padding_0s == padded_len(len) - (len + 64 + 1);

	assert num_padding_0s == num_padding_zeroes(len);
	
	assert num_padding_0s == NumPaddingZeroes(len);
	assert num_zero_ints * 32 + num_zeroes == NumPaddingZeroes(len) + 64;

	// Prove that we reached the correct integer value, before adding the length
	ghost var padding := num_zero_ints * 32 + num_zeroes;	
	assert(seq_to_int(data[..], len + 1) == 2*seq_to_int(data[..], len) + 1);
	assert(padded_len(len) - padding == len + 1);
	
	assert 0 <= padding < padded_len(len); 
	assert forall bit_index :: 0 <= bit_index < padding ==> get_array_bit(bit_index, data, padded_len(len)) == 0;
	assert padded_len(len) == PaddedLength(len);
	assert padding == NumPaddingZeroes(len) + 64;
	
	// Can verify everything above without timing out 
	/*
	//lemma_seq_to_int_and_zeroes(data, padded_len(len));
	lemma_seq_to_int_and_zeroes2(data, padded_len(len), padding);
	assert(seq_to_int(data, padded_len(len)) == Power2(padding) * seq_to_int(data, len + 1));
	
	// Current work in progress:
	assert(Power2(NumPaddingZeroes(len) + 64) * seq_to_int(data, len + 1) ==
			Power2(1 + NumPaddingZeroes(len) + 64) * seq_to_int(data, len) + Power2(NumPaddingZeroes(len) + 64) );

	assert(seq_to_int(data, PaddedLength(len)) == Power2(1 + NumPaddingZeroes(len) + 64) * seq_to_int(data, len) + Power2(NumPaddingZeroes(len) + 64) );
	assert(seq_to_int(data, PaddedLength(len) - 32) == 
			Power2(1 + NumPaddingZeroes(len) + 64 - 32) * seq_to_int(data, len) + Power2(NumPaddingZeroes(len) + 64 - 32) );
	*/

	/*
	ghost var padded_basic_len := len + 1 + num_padding_zeroes;
	ghost var padded_len_plus_zero := padded_basic_len + 32;
	ghost var padded_len_plus_len  := padded_len_plus_zero + 32;
	assert(padded_basic_len - num_padding_zeroes == len + 1);
	assert 0 <= num_padding_zeroes < padded_basic_len;
	assert forall bit_index :: 0 <= bit_index < num_padding_zeroes ==> get_array_bit(bit_index, data, padded_basic_len) == 0;
	lemma_seq_to_int_and_zeroes2(data, padded_basic_len, num_padding_zeroes);
	assert(seq_to_int(data, padded_basic_len) == Power2(num_padding_zeroes) * seq_to_int(data, len + 1));
	lemma_extend_by_int(data, padded_basic_len);
	ghost var next_to_last_int := padded_len_plus_zero / 32 - 1;
	assert seq_to_int(data, padded_len_plus_zero) == Power2(32) * seq_to_int(data, padded_basic_len) + data[next_to_last_int];
	*/

	//assert(seq_to_int(data, padded_len(len)-32) == Power2(padding-32) * seq_to_int(data, len + 1));
	//assert(seq_to_int(data, padded_len(len)) == Power2(NumPaddingZeroes(len) + 64) * seq_to_int(data, len + 1));
	//assert seq_to_int(data, padded_len(len)) == old(seq_to_int(data, len)) * Power2(1 + NumPaddingZeroes(len) + 64) + Power2(NumPaddingZeroes(len) + 64);

	//assert forall bit_index :: 32 * (one_bit_index + 1) <= bit_index < padded_len(len) ==> get_array_bit(padded_len(len) - bit_index, data, padded_len(len)) == 0;
		
	//assert(forall i :: 0 <= i < data.Length ==> word(data[i]));

	/*
	// Finally, set the last int to the original length
	var last_int := padded_len(len) / 32 - 1;
	data[last_int] := len;
	lemma_extend_by_int(data, padded_len(len));
	// The following verifies but takes many minutes
	assert(seq_to_int(data, padded_len(len)) == seq_to_int(data, padded_len(len) - 32) * Power2(32) + data[last_int]);
	assert(padded_len(len) == PaddedLength(len));
	assert(seq_to_int(data, PaddedLength(len)) == seq_to_int(data, padded_len(len) - 32) * Power2(32) + len);
	*/
}


ghost method lemma_mod_512_is_mod_32(a:int) 
	requires a % 512 == 0;
	ensures  a % 32 == 0;
{
}

method padding_add_len(data: array<int>, len: int)
	requires word(len);
	requires len <= Power2(32) - 1 && len < Power2(64);
	requires data != null;	
	requires data.Length * 32 == len;
	requires 0 <= PaddedLength(len) < data.Length * 32;		// Make padding easier
	requires PaddedLength(len) < Power2(32);	
	requires forall i :: 0 <= i < data.Length ==> word(data[i]);
	requires seq_to_int(data[..], len) < Power2(len);
	modifies data;
	ensures forall i :: 0 <= i < data.Length ==> word(data[i]);
	ensures seq_to_int(data[..], PaddedLength(len)) == seq_to_int(data[..], PaddedLength(len) - 32) * Power2(32) + len;
	ensures seq_to_int(data[..], PaddedLength(len) - 32) == old(seq_to_int(data[..], PaddedLength(len) - 32));
	ensures seq_to_int(data[..], len) == old(seq_to_int(data[..], len));
{
	// Finally, set the last int to the original length
	var last_int := padded_len(len) / 32 - 1;
	data[last_int] := len;
	lemma_extend_arr_by_int(data, padded_len(len));
	// The following verifies but takes many minutes
	assert(seq_to_int(data[..], padded_len(len)) == seq_to_int(data[..], padded_len(len) - 32) * Power2(32) + data[last_int]);
	assert(padded_len(len) == PaddedLength(len));
	assert(seq_to_int(data[..], PaddedLength(len)) == seq_to_int(data[..], PaddedLength(len) - 32) * Power2(32) + len);
}

///////////////////////////////////////////////////////////////
// Prove mathematical properties of pad_message_with_zeroes 
///////////////////////////////////////////////////////////////

// The following verifies successfully.  Body commented out to speed proofs
ghost method lemma_pad_message(data: array<int>, len: int, padding: int)
	requires word(len);
	requires len <= Power2(32) - 1 && len < Power2(64);
	requires data != null;	
	requires data.Length * 32 >= len;
	requires data.Length * 32 > padded_len(len);		// Make padding easier
	requires padded_len(len) < Power2(32);	
	requires forall i :: 0 <= i < data.Length ==> word(data[i]);
	requires seq_to_int(data[..], len) < Power2(len);

	requires padding == NumPaddingZeroes(len) + 64;

	requires forall i :: 0 <= i < data.Length ==> word(data[i]);
	requires forall bit_index :: 0 <= bit_index < NumPaddingZeroes(len) + 64 ==> get_array_bit(bit_index, data, PaddedLength(len)) == 0;
	requires seq_to_int(data[..], len + 1) == 2*seq_to_int(data[..], len) + 1;
	ensures  additive_padding(data, len, padding, PaddedLength(len));   // same as: seq_to_int(data, PaddedLength(len)) == Power2(1 + padding) * seq_to_int(data, len) + Power2(padding);
	ensures  seq_to_int(data[..], PaddedLength(len)) == Power2(32) * seq_to_int(data[..], PaddedLength(len) - 32);  // This one times out in VS, but verifies at the cmd line
/*
{
	assert(zero_seq(data, PaddedLength(len), padding));
	lemma_seq_to_int_and_zeroes2(data, PaddedLength(len), padding);

	calc {
		seq_to_int(data, PaddedLength(len));
		==
		Power2(padding) * seq_to_int(data, len + 1);
		==
		Power2(1 + padding) * seq_to_int(data, len) + Power2(padding);
	}
	
	assert(additive_padding(data, len, padding, PaddedLength(len)));

	assert(padding - 32 > 0);
	assert(PaddedLength(len) - 32 > 0);
	lemma_seq_to_int_and_zeroes2(data, PaddedLength(len), 32);
	assert(seq_to_int(data, PaddedLength(len)) == Power2(32) * seq_to_int(data, PaddedLength(len) - 32));
}
*/

// For some reason (triggers?) wrapping this in a static function makes Dafny happy
static function additive_padding(arr: array<int>, len: int, padding: int, padded_length: int) : bool
	requires arr != null;
	requires 0 <= len < arr.Length * 32;	
	requires 0 <= padded_length < arr.Length * 32;
	requires len < Power2(32);
	requires padded_length < Power2(32);
	requires forall i :: 0 <= i < arr.Length ==> word(arr[i]);		
	requires padding >= 0;
	reads arr;
{
	seq_to_int(arr[..], padded_length) == Power2(1 + padding) * seq_to_int(arr[..], len) + Power2(padding)
}

// Verifies successfully -- commented out to speed things up
ghost method lemma_seq_to_int_and_zeroes2(arr:array<int>, len:int, num_zeroes:int)
	requires arr != null;
	requires 0 <= len < arr.Length * 32;	
	requires len < Power2(32);
	requires forall i :: 0 <= i < arr.Length ==> word(arr[i]);	
	requires 0 <= num_zeroes < len;
	requires zero_seq(arr, len, num_zeroes);
	ensures  len > 0 ==> seq_to_int(arr[..], len) == Power2(num_zeroes) * seq_to_int(arr[..], len - num_zeroes);
	/*
{
	if (num_zeroes >= 1) {
		lemma_get_array_bit(arr, len, num_zeroes);
		ghost var len_prime := len -1;
		ghost var num_zeroes_prime := num_zeroes - 1;
		assert forall i :: 0 <= i < num_zeroes ==> get_array_bit(i, arr, len) == 0;
		assert zero_seq(arr, len, num_zeroes);
		assert zero_seq(arr, len-1, num_zeroes-1);
		assert zero_seq(arr, len_prime, num_zeroes_prime);
		assert forall i :: 0 <= i < num_zeroes_prime ==> get_array_bit(i, arr, len_prime) == 0;
		lemma_seq_to_int_and_zeroes2(arr, len_prime, num_zeroes_prime);
		assert len - 1 > 0 ==> seq_to_int(arr, len - 1) == Power2(num_zeroes - 1) * seq_to_int(arr, (len - 1) - (num_zeroes-1));
		lemma_get_array_bit(arr, len, num_zeroes);
		assert forall i :: 0 <= i < num_zeroes - 1 ==> get_array_bit(i, arr, len - 1) == 0;
		lemma_seq_to_int_and_zeroes2(arr, len - 1, num_zeroes - 1);
		assert len_prime > 0 ==> seq_to_int(arr, len_prime) == Power2(num_zeroes_prime) * seq_to_int(arr, len_prime - num_zeroes_prime);
		assert len - 1 > 0 ==> seq_to_int(arr, len - 1) == Power2(num_zeroes - 1) * seq_to_int(arr, (len - 1) - (num_zeroes-1));
	} else {
		assert Power2(num_zeroes) == 1;
		assert seq_to_int(arr, len - num_zeroes) == seq_to_int(arr, len);
	}

}*/
	
static function zero_seq(arr:array<int>, len:int, num_zeroes:int) : bool
	reads arr;
	requires arr != null;
	requires 0 <= len <= arr.Length * 32;	
	//requires 2 <= len < Power2(32);	
	requires len < Power2(32);	
	requires forall i :: 0 <= i < arr.Length ==> word(arr[i]);	
	requires num_zeroes < len;
{
	(forall i :: 0 <= i < num_zeroes ==> get_array_bit(i, arr, len) == 0)
}

// Verifies successfully -- commented out to speed things up
ghost method lemma_get_array_bit(arr:array<int>, len:int, num_zeroes:int)
	requires arr != null;
	requires 0 < len < arr.Length * 32;	
	//requires 2 <= len < Power2(32);	
	requires len < Power2(32);	
	requires forall i :: 0 <= i < arr.Length ==> word(arr[i]);	
	requires 0 <= num_zeroes < len;
	//ensures  get_array_bit(1, arr, len) == get_array_bit(0, arr, len - 1);
	//ensures  (forall i :: 0 <= i < num_zeroes ==> get_array_bit(i, arr, len) == 0) ==> 	(forall i :: 0 <= i < num_zeroes - 1 ==> get_array_bit(i, arr, len - 1) == 0);	
	ensures zero_seq(arr, len, num_zeroes) ==> zero_seq(arr, len-1, num_zeroes-1);
	//forall i :: 0 <= i < len ==> get_array_bit(i, arr, len) == get_array_bit(i, arr, len - 1)
/*
{
	assert zero_seq(arr, len, num_zeroes) ==> (forall i :: 1 <= i < num_zeroes ==> get_array_bit(i, arr, len) == get_array_bit(i-1, arr, len-1));
	assert zero_seq(arr, len, num_zeroes) ==> (forall i :: 1 <= i < num_zeroes ==> get_array_bit(i-1, arr, len-1) == get_array_bit(i, arr, len) && get_array_bit(i, arr, len) == 0);
	//assert zero_seq(arr, len, num_zeroes) ==> (forall i :: 1 <= i < num_zeroes ==> get_array_bit(i-1, arr, len-1) == 0);	// Can't get this

	if zero_seq(arr, len, num_zeroes) {
		forall i | 0 <= i < num_zeroes - 1		// Changing this to 0 <= i < num_zeroes-1, instead of 1 <= i < num_zeroes makes the proof go through
			ensures get_array_bit(i, arr, len-1) == 0;
		{
			calc {
				0;
				==
				get_array_bit(i+1, arr, len);
				==
				get_array_bit(i, arr, len-1);
			}
		}
	}
}
*/


///////////////////////////////////////////////////////////////
// Prove mathematical properties of padding_add_len 
///////////////////////////////////////////////////////////////

ghost method lemma_extend_arr_by_int(arr:array<int>, len:int)
	requires arr != null;
	requires len % 32 == 0;
	requires arr.Length >= 2;
	requires len == arr.Length * 32;
	requires len < Power2(32);
	requires forall i :: 0 <= i < arr.Length ==> word(arr[i]);	
	ensures  seq_to_int(arr[..], len) == Power2(32) * seq_to_int(arr[..], len - 32) + arr[len / 32 - 1];
{
	assert arr[0..|arr[..]|-1] + arr[|arr[..]|-1..] == arr[..];
	calc {
		seq_to_int(arr[..], len);
		{ lemma_seq_to_int_split32(arr, len); }
		Power2(32) * seq_to_int(arr[0..|arr[..]|-1], len - 32) + seq_to_int(arr[|arr[..]|-1..], 32);
		{ lemma_a2i_is_int(arr[|arr[..]|-1..], 32); }
		Power2(32) * seq_to_int(arr[0..|arr[..]|-1], len - 32) + arr[len / 32 - 1];
		calc {
			seq_to_int(arr[0..|arr[..]|-1], len - 32);
			{ lemma_seq_to_int_ignores_excess_data(arr[0..|arr[..]|-1], arr[|arr[..]|-1..], len - 32); }
			seq_to_int(arr[..], len - 32);
		}
		Power2(32) * seq_to_int(arr[..], len - 32) + arr[len / 32 - 1];
	}

}
	
ghost method lemma_seq_to_int_split32(arr:array<int>, len:int)
	requires arr != null;
	requires arr.Length >= 2;
	requires len == arr.Length * 32;
	requires len < Power2(32);
	requires forall i :: 0 <= i < arr.Length ==> word(arr[i]);	
	ensures  seq_to_int(arr[..], len) == Power2(32) * seq_to_int(arr[0..|arr[..]|-1], len - 32) + seq_to_int(arr[|arr[..]|-1..], 32);
{
	assert |arr[0..|arr[..]|-1]| == arr.Length - 1;
	assert arr[0..|arr[..]|-1] + arr[|arr[..]|-1..] == arr[..];
	lemma_seq_to_int_split(arr[0..|arr[..]|-1], arr[|arr[..]|-1..], len - 32, 32);

	assert seq_to_int(arr[0..|arr[..]|-1] + arr[|arr[..]|-1..], len - 32 + 32) == Power2(32) * seq_to_int(arr[0..|arr[..]|-1], len - 32) + seq_to_int( arr[|arr[..]|-1..], 32);
	assert seq_to_int(arr[0..|arr[..]|-1] + arr[|arr[..]|-1..], len - 32 + 32) == seq_to_int(arr[..], len);
}
	

ghost method lemma_seq_to_int_ignores_excess_data(arr:seq<int>, singleton:seq<int>, len:int)
	requires 0 <= len <= |arr| * 32;
	requires len < Power2(32);
	requires |singleton| == 1;		
	requires forall i :: 0 <= i < |arr| ==> word(arr[i]);	
	requires word(singleton[0]);
	ensures  seq_to_int(arr + singleton, len) == seq_to_int(arr, len);
{
	if (len == 0) {

	} else {
		lemma_seq_to_int_ignores_excess_data(arr, singleton, len - 1);
		assert seq_to_int(arr + singleton, len - 1) == seq_to_int(arr, len - 1);
		assert seq_to_int(arr + singleton, len) == 2 * seq_to_int(arr + singleton, len - 1) + get_seq_bit(0, arr + singleton, len);
	}
}

ghost method {:timeLimit 30}lemma_seq_to_int_split(arr:seq<int>, singleton:seq<int>, len:int, amt_of_singleton:int)
	requires len % 32 == 0;
	requires len == |arr| * 32;
	requires len < Power2(32);
	requires len + amt_of_singleton < Power2(32);
	requires |singleton| == 1;
	requires 0 <= amt_of_singleton <= 32;
	requires forall i :: 0 <= i < |arr| ==> word(arr[i]);	
	requires word(singleton[0]);
	ensures  seq_to_int(arr + singleton, len + amt_of_singleton) == Power2(amt_of_singleton) * seq_to_int(arr, len) + seq_to_int(singleton, amt_of_singleton);
{
	var data := arr + singleton;
	var len_plus_amt := len + amt_of_singleton;
	
	assert data[len / 32] == singleton[0];

	if (amt_of_singleton > 0) {	
		assert (len + amt_of_singleton - 1) % 32 == (amt_of_singleton - 1) % 32;

		var q := len / 32;
		var r := len % 32;
		assert len == 32 * q + r;
		assert r == 0;
		assert len == 32 * q;
		assert amt_of_singleton - 1 < 32;
		assert len + amt_of_singleton - 1 < 32 * q + 32;
		assert 32 * q <= len + amt_of_singleton - 1 ;
		assert (len + amt_of_singleton - 1) / 32  == len / 32;
	}
	

	if (amt_of_singleton == 0) {
		assert Power2(amt_of_singleton) == 1;
		assert seq_to_int(singleton, amt_of_singleton) == 0;

		calc {
			seq_to_int(arr + singleton, len + amt_of_singleton);
			seq_to_int(arr + singleton, len); 
			{ lemma_seq_to_int_ignores_excess_data(arr, singleton, len); }
			seq_to_int(arr, len);
		}
		assert seq_to_int(arr + singleton, len + amt_of_singleton) == Power2(amt_of_singleton) * seq_to_int(arr, len) + seq_to_int(singleton, amt_of_singleton);
	} else {
		lemma_seq_to_int_split(arr, singleton, len, sub2(amt_of_singleton, 1));
		assert seq_to_int(data, len + sub2(amt_of_singleton, 1)) == Power2(sub2(amt_of_singleton, 1)) * seq_to_int(arr, len) + seq_to_int(singleton, sub2(amt_of_singleton, 1));

		calc {
			seq_to_int(data, len_plus_amt);
			seq_to_int(data, len + amt_of_singleton);
			2 * seq_to_int(data, len + sub2(amt_of_singleton, 1)) + get_seq_bit(0, data, len + amt_of_singleton);
			2 * (Power2(sub2(amt_of_singleton, 1)) * seq_to_int(arr, len) + seq_to_int(singleton, sub2(amt_of_singleton, 1))) + get_seq_bit(0, data, len + amt_of_singleton);
			Power2(amt_of_singleton) * seq_to_int(arr, len) + 2 * seq_to_int(singleton, sub2(amt_of_singleton, 1)) + get_seq_bit(0, data, len + amt_of_singleton);
			calc {
				get_seq_bit(0, data, len + amt_of_singleton);
				get_bit(31 - (len + amt_of_singleton - 1) % 32, data[(len + amt_of_singleton - 1)/32]);
				calc {
					(len + amt_of_singleton - 1) % 32;
					(amt_of_singleton - 1) % 32;
				}
				get_bit(31 - (amt_of_singleton - 1) % 32, data[(len + amt_of_singleton - 1)/32]);
				get_bit(31 - (amt_of_singleton - 1) % 32, singleton[0]);
				get_seq_bit(0, singleton, amt_of_singleton);
			}				
			Power2(amt_of_singleton) * seq_to_int(arr, len) + seq_to_int(singleton, amt_of_singleton);
		}
		assert seq_to_int(data, len_plus_amt) == Power2(amt_of_singleton) * seq_to_int(arr, len) + seq_to_int(singleton, amt_of_singleton);
		assert seq_to_int(arr + singleton, len + amt_of_singleton) == Power2(amt_of_singleton) * seq_to_int(arr, len) + seq_to_int(singleton, amt_of_singleton);
	}
}

// Needed so we can use it as a justification inside of a calc statement
ghost method lemma_power2_adds(x:int, y:int)
	requires x >= 0 && y >= 0;
	ensures Lemma_Power2TurnsAdditionIntoMultiplication(x, y);
{
}

ghost method lemma_a2i_is_int(arr:seq<int>, len:int) 
	requires len == 32;
	requires len <= |arr| * 32;
	requires len < Power2(32);
	requires forall i :: 0 <= i < |arr| ==> word(arr[i]);	
	ensures  seq_to_int(arr[..], len) == arr[0];
{
	lemma_equivalences();
	lemma_a2i_is_int_decomposition(arr, len, 0);
	lemma_int_decomposition(arr[0], len, len);
}

ghost method {:timeLimit 30}lemma_a2i_is_int_decomposition(arr:seq<int>, len:int, num_bits_sub:int)
	requires 0 <= num_bits_sub <= len == 32;
	requires len <= |arr| * 32;
	requires len < Power2(32);
	requires forall i :: 0 <= i < |arr| ==> word(arr[i]);	
	requires (forall x:int, amt:int :: word(x) && 0 <= amt <= 32 ==> right_shift(x, amt) == RightShift32(x, amt));
	ensures  seq_to_int(arr[..], len - num_bits_sub) == int_decomposition(arr[0], len, len - num_bits_sub);
	decreases len - num_bits_sub;
{
	if (num_bits_sub == 32) {
		assert seq_to_int(arr[..], len - num_bits_sub) == int_decomposition(arr[0], len, len - num_bits_sub);
	} else if (num_bits_sub == 0) {
		assert seq_to_int(arr[..], len) ==	2 * seq_to_int(arr[..], len - 1) + get_seq_bit(0, arr, len);
		assert get_seq_bit(0, arr, len) == get_bit(0, arr[0]);
		assert seq_to_int(arr[..], len) ==	2 * seq_to_int(arr[..], len - 1) + get_bit(0, arr[0]);
		assert int_decomposition(arr[0], len, len) == 2 * int_decomposition(arr[0], len, len - 1) + get_bit(0, arr[0]);
		lemma_a2i_is_int_decomposition(arr, len, 1);
		assert seq_to_int(arr[..], len - num_bits_sub) == int_decomposition(arr[0], len, len - num_bits_sub);
	} else {
		if (len - num_bits_sub - 1 > 0) {
			calc {
				seq_to_int(arr[..], len - num_bits_sub);
				seq_to_int(arr[..], sub2(len, num_bits_sub));
				2 * seq_to_int(arr[..], sub2(sub2(len, num_bits_sub), 1)) + get_seq_bit(0, arr, sub2(len, num_bits_sub));
				{ lemma_a2i_is_int_decomposition(arr, len, num_bits_sub + 1); }
				2 * int_decomposition(arr[0], len, sub2(sub2(len, num_bits_sub), 1)) + get_seq_bit(0, arr, sub2(len, num_bits_sub));
				calc {
					2 * int_decomposition(arr[0], len, sub2(len, num_bits_sub) - 1) + get_seq_bit(0, arr, sub2(len, num_bits_sub));
					2 * int_decomposition(arr[0], len, sub2(len, num_bits_sub) - 1) + get_bit(num_bits_sub, arr[0]);
					int_decomposition(arr[0], len,  sub2(len, num_bits_sub));					
				}
				int_decomposition(arr[0], len,  sub2(len, num_bits_sub));
			}
			/*
			assert seq_to_int(arr[..], len - num_bits_sub) == 2 * seq_to_int(arr[..], len - num_bits_sub - 1) + get_seq_bit(0, arr, len - num_bits_sub);
			assert int_decomposition(arr[0], len, len - num_bits_sub) == 2 * int_decomposition(arr[0], len, len - num_bits_sub - 1) + get_bit(num_bits_sub, arr[0]);
			lemma_a2i_is_int_decomposition(arr, len, num_bits_sub + 1);
			*/
			assert seq_to_int(arr[..], len - num_bits_sub) == int_decomposition(arr[0], len, len - num_bits_sub);
		}
	}
	assert seq_to_int(arr[..], len - num_bits_sub) == int_decomposition(arr[0], len, len - num_bits_sub);
}

function int_decomposition(x:int, len:int, num_bits:int) : int
	requires 0 <= num_bits <= len <= 32;
	requires 0 <= x < Power2(len);
	requires word(x);
	requires (forall x:int, amt:int :: word(x) && 0 <= amt <= 32 ==> right_shift(x, amt) == RightShift32(x, amt));
{
	if num_bits <= 0 then 0 else
		2 * int_decomposition(x, len, num_bits - 1) + get_bit(len - num_bits, x)
} 

ghost method lemma_int_decomposition(x:int, len:int, num_bits:int) 
	requires 0 <= num_bits <= len <= 32;
	requires 0 <= x < Power2(len);
	requires word(x);
	requires (forall x:int, amt:int :: word(x) && 0 <= amt <= 32 ==> right_shift(x, amt) == RightShift32(x, amt));
	ensures  int_decomposition(x, len, len) == x;
{
	assert Power2(0) == 1;
	calc {
		int_decomposition(x, len, len);
		{ lemma_int_decomposition_is_int_div(x, len, len); }
		int_div(x, Power2(len - len));
		int_div(x, 1);
		{ lemma_div_by_multiple_simple(x, 1); }
		x;
	}
}

ghost method lemma_int_decomposition_is_int_div(x:int, len:int, num_bits:int) 
	requires 0 <= num_bits <= len <= 32;
	requires 0 <= x < Power2(len);
	requires word(x);
	requires (forall x:int, amt:int :: word(x) && 0 <= amt <= 32 ==> right_shift(x, amt) == RightShift32(x, amt));
	requires Lemma_Power2IsIncreasing(num_bits, len);
	ensures int_decomposition(x, len, num_bits) == int_div(x, Power2(len - num_bits));		
{
	if (num_bits == 0) {
		assert int_decomposition(x, len, num_bits) == int_div(x, Power2(len - num_bits));
	} else {
		var d := int_div(x, Power2(len - num_bits));

		calc {
			int_decomposition(x, len, num_bits);
			2 * int_decomposition(x, len, num_bits - 1) + get_bit(len - num_bits, x);
			2 * int_div(x, Power2(len - num_bits + 1)) + get_bit(len - num_bits, x);
			{ lemma_pow2_div(x, len - num_bits); }
			2 * int_div(d, 2) + get_bit(len - num_bits, x);
		}	
			
		if (d % 2 == 0) {
			lemma_even_div(d);
			assert 2 * int_div(d, 2) == d;
			assert int_decomposition(x, len, num_bits) == d + get_bit(len - num_bits, x);
			assert get_bit(len - num_bits, x) == RightShift32(x, len-num_bits) % 2;
			lemma_right_shift_is_div_pow2(x, len-num_bits);
		} else {
			lemma_odd_div(d);
			assert 2 * int_div(d, 2) + 1 == d;
			assert get_bit(len - num_bits, x) == RightShift32(x, len-num_bits) % 2;
			lemma_right_shift_is_div_pow2(x, len-num_bits);
		}
	}
}


