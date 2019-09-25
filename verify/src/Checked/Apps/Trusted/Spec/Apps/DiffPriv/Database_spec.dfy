include "../../../../Checked/Libraries/BigNum/Word32.dfy"
include "Math_spec.dfy"

datatype Row = Row_ctor(nonce:seq<int>, data:seq<int>);

function RowValid(row:Row):bool
{
    forall i :: 0 <= i < |row.data| ==> Word32(row.data[i])
}

function DatabaseValid(db:seq<Row>):bool
{
    forall i:int :: 0 <= i < |db| ==> RowValid(db[i])
}

function DatabasesIdenticalExceptForOneRow (db1:seq<Row>, db2:seq<Row>, diff_row:int):bool
{
    |db1| == |db2| &&
    (forall i :: 0 <= i < |db1| && i != diff_row ==> db1[i] == db2[i])
}

function DatabasesSimilar (db1:seq<Row>, db2:seq<Row>):bool
{
    exists diff_row :: DatabasesIdenticalExceptForOneRow(db1, db2, diff_row)
}

function DatabaseContainsNonce (db:seq<Row>, nonce:seq<int>) : bool
{
    exists i:int :: 0 <= i < |db| && db[i].nonce == nonce
}
