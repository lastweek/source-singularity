include "../../../Assembly.dfy"

function BigEndianIntegerValue(os:seq<int>) : nat
	decreases |os|;
	requires ByteSeq(os);
{
	if (os==[]) then
		0
	else
		BigEndianIntegerValue(os[0..|os|-1])*256 + os[|os|-1]
}

