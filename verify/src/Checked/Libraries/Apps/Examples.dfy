function method word(x:int):bool
function method and (x:int, y:int):int
function method or  (x:int, y:int):int
function method xor (x:int, y:int):int

// mutual summary ensures that M_1[r_1] == M_2[r_2]
// ghost method Sample (M:map<int,int>) returns (r:int)
//   requires (forall x:int, y:int :: x in M && y in M ==> M[x] == M[y] ==> x == y);
method serialPortOut (x:int)
method serialPortIn () returns (r:int)
  ensures (word(r));
method sample (ghost M:map<int, int>) returns (r:int)

ghost method SampleLemma(p:int, M:map<int,int>)
  ensures (forall x:int :: x in M ==> M[x] == xor(x,p));

ghost method XorLemmas()
  ensures (forall x:int::xor(x, x) == 0);
  ensures (forall x:int::word(x) ==> xor(x, 0) == x);
  ensures (forall x:int, y:int::xor(x, y) == xor(y, x));
  ensures (forall x:int, y:int:: word(x) && word(y) ==> word(xor(x, y)));
  ensures (forall x:int, y:int, z:int:: xor(x, xor(y,z)) == xor(y, xor(x,z)));
  ensures (forall x:int, y:int:: xor(x,xor(y,x)) == y);

method XorIdentity(a:int) returns(r:int)
  requires word(a);
  ensures  r == a;
{
  XorLemmas();
  r := xor(xor(a, a), a);
}

method pad_one_block (p:int) returns (r:int)
  requires word(p);
//  ensures r == One_Time_Pad(p, old(sample_index));
//  ensures (exists s:int :: sampleCall(old(index), index, s) && r == xor(p,s)); 
//  relational verification should verify that true ==> r<1> == r<2>
{
  XorLemmas();
  // var i:int := 0;
  var k:int;
  ghost var M:map<int,int>;
  SampleLemma(p, M);
  k := sample(M);
  r := xor(k,p);
  assert r == xor(k,p);
  // return r;
}


method one_time_pad( ) returns ()
  modifies this;
//  add requirement on maintaining the serial port queue later
//  requires ps != null;
//  requires forall i :: 0<= i < index ==> word(ps[i]);
//  ensures  rs != null;
//  ensures  ps.Length == rs.Length;
//  ensures  forall i :: 0<= i < index ==> rs[i] == xor (k, ps[i]);   
//  ensures  forall i :: 0<= i < index ==> word(rs[i]);   
{
  // read in a value (plain text) from serial port
  var length:int := 10;
  var index:int := 0;
  var p:int := 0;
  var r:int := 0;
  //while (index < length) {
    p := serialPortIn();
    r := pad_one_block (p);
    // write the xor(p,k) (encryption) to the serial port
    serialPortOut(r);
    index := index+1;
  //}
}

/* encryption of multiple blocks. This function ensures that:
   1. each block b is encrypted into xor(b,k), where k is the global key
   2. each encrypted blocks are still words
*/
/*
method Encrypt (ps: array<int>, k:int) returns (rs: array<int>)
  requires ps != null;
  requires forall i :: 0<= i < ps.Length ==> word(ps[i]);
  requires word(k);
  ensures  rs != null;
  ensures  ps.Length == rs.Length;
  ensures  forall i :: 0<= i < ps.Length ==> rs[i] == xor (k, ps[i]);   
  ensures  forall i :: 0<= i < ps.Length ==> word(rs[i]);   
{   
  var index:int := 0;   
      rs := new int[ps.Length];

  while (index < ps.Length)      
    invariant 0 <= index <= ps.Length;      
	invariant forall i :: 0 <= i < index ==> rs[i] == xor(k, ps[i]);   
  {      
    if (index == ps.Length) {break;}      
    rs := encrypt_nat(ps, k, index);
    index := index + 1;
  }   
}
*/

////// PwdBox-Game0

/* common declarations for Hash and sample */
ghost var global_sample_index:int;
ghost var randomSource:map<int, int>;

// these methods are defined in Entry.beat
function method word(x:int):bool
method serialPortOut (x:int)
method serialPortIn () returns (r:int)
  ensures (word(r));
method sample (ghost M:map<int, int>) returns (r:int)
  modifies this;
  ensures Hashed == old(Hashed);
  ensures randomSource[old(global_sample_index)] == r;
  ensures old(global_sample_index)+1 == global_sample_index;

function SampleVal(index:int):int

ghost method SampleLemmaID(M:map<int,int>)
  ensures (forall x :: x in M ==> M[x] == x);

ghost var Hashed:map<Tri, int>;
function RdmOracle (tri:Tri, ret:int, HashedOld:map<Tri, int>, Hashed:map<Tri, int>, index:int, randomSource:map<int, int>) : bool
{
     (tri in HashedOld ==> Hashed == HashedOld && Hashed[tri] == ret /*&& index == index+1*/) // increase the index in random source anyway
  && (!(tri in HashedOld) ==> SampleVal(index) == ret && Hashed == HashedOld[tri := ret])
}

method Hash(pwd:int, salt:int, k:int) returns (r:int)
  modifies this; 
  ensures RdmOracle(Triple(pwd, salt, k), r, old(Hashed), Hashed, old(global_sample_index), randomSource);
  ensures global_sample_index == old(global_sample_index)+1;

/* implementation */
datatype Tri = Triple(Pwd:int, Salt:int, Key:int);

method init (pwd:int, key:int) returns (hash:int, salt:int)
  modifies this;
  ensures randomSource[old(global_sample_index)] == salt;
  ensures RdmOracle(Triple(pwd, salt, key), hash, old(Hashed), Hashed, old(global_sample_index)+1, randomSource);
  ensures global_sample_index == old(global_sample_index)+2;
{
    ghost var M:map<int, int>;
    SampleLemmaID(M);
    salt := sample(M);
    hash := Hash(pwd, salt, key);
    // assert false;
} 

method verify (pwd:int, salt:int, key:int) returns (hash:int) 
  modifies this; 
  ensures RdmOracle(Triple(pwd, salt, key), hash, old(Hashed), Hashed, old(global_sample_index), randomSource);
  ensures global_sample_index == old(global_sample_index)+1;
{
    hash := Hash(pwd, salt, key);
}

/* game definition and check*/

// abstract adversary
method adversary(hash:int, salt:int) returns (guess:int, key:int)
  ensures (exists x:int, y:int, u:int :: RdmOracle(Triple(x, y, key), u, old(Hashed), Hashed, old(global_sample_index), randomSource));
{
}
/*
function Permutation(m:map<int, int>) : bool
{
   forall i:int, j:int :: i in m ==> j in m ==> i != j ==> (m[i] != m[j]) 
}
*/

method Game () returns (ghost g_hash_db:int, ghost g_hash_verify:int, ghost g_pwd:int, ghost g_key:int, ghost g_k:int)
  modifies this;
{
    ghost var M:map<int, int>;
    var pwd:int, key:int, salt:int, hash_verify:int, hash_db:int, g:int, k:int;
    SampleLemmaID(M);
    // game 1
    pwd := sample(M);
    key := sample(M);
    hash_db, salt := init(pwd, key);
    // adversary may call oracle with 
    // arbitrary values
    g, k := adversary(hash_db, salt);
    
    hash_verify := verify(g, salt, key);
    // succ := (hash_db == hash_verify);
    g_hash_db := hash_db;
    g_hash_verify := hash_verify;
    g_pwd := pwd;
    g_key := key;
    g_k := k;
    //var t:Tri := Triple(g, salt, key);
    //hash2, m := Hash(t, rn6, m);
}

/*
method OpenDictSecure( ) 
      returns (perm:map<int, int>, hash_db:int, hash_verify:int, g:int, pwd:int, salt:int, h:int, adv_pwd:int, adv_salt:int, adv_key:int,
               hash_db':int, hash_verify':int, g':int, pwd':int, salt':int, key':int, h':int)
  modifies this;
  requires global_sample_index == 0;
  requires Map == map[];
  ensures ( (SampleVal(0) == SampleVal(6) && SampleVal(1) == SampleVal(7) && SampleVal(2) == SampleVal(8) && SampleVal(3) == SampleVal(9)
          && SampleVal(4) == SampleVal(10) && SampleVal(5) == SampleVal(11)) ==> 
    (pwd'!=g') && (adv_key!=key') ==> ((hash_db==hash_verify) == (hash_db'==hash_verify')));
    // Hence, we have
    //    P(hash1==hash2) 
    // <= P(hash1'==hash2') + P(tmp_key == key') + P(pwd' == g') 
    // =  1/2^n + 1/2^k + 1/2^m, where n is the length of the hash value, k the length of the key, and m is the length of the password
{
    ghost var M:map<int, int>;
    SampleLemma(M);
    // game 1
    pwd := sample(M);
    assert global_sample_index == 1;
    hash_db, salt := init(pwd);
    assert global_sample_index == 4;
    // adversary may call oracle with 
    // arbitrary values
    adv_pwd, adv_salt, adv_key  := *,*,*;
    h := Hash(adv_pwd, adv_salt, adv_key);
    assert global_sample_index == 5;
    g := guess(hash_db, salt, h);
    
    hash_verify := verify(g, salt);
    assert global_sample_index == 6;
    //var t:Tri := Triple(g, salt, key);
    //hash2, m := Hash(t, rn6, m);

    // game 2
    pwd' := sample(M);  
    key' := sample(M);  
    salt' := sample(M); 
    hash_db' := sample(M);
    h' := sample(M);    
    g' := guess(hash_db', salt', h');
    hash_verify' := sample(M);
}
*/

/*
// version 1, we want to calculate P(hash1 == hash2)
method PwdBox1() returns (b:bool)
{
    var pwd:int := sample();
    var salt:int := sample();
    var key:int  := sample();
    var t:Tri := Triple(pwd,salt,key);
    var m:map<Tri,int>;
    // version 1
    var hash1:int;
    hash1, m := Hash(t,m);
    
    // adverary can call HA
    var tmp_pwd, tmp_salt, tmp_key := *, *, *;
    var L:set<int> := {tmp_key};
    var r';
    r', m := Hash( Triple(tmp_pwd, tmp_salt, tmp_key), m);
    var g:int := guess(hash1, salt);
    
    var t':Tri := Triple(g, salt, key);
    var hash2:int;
    hash2, m := Hash(t', m);
    return (hash1 == hash2);
}

// version 2
method PwdBox2() returns (b:bool)
{
    var pwd:int := sample();
    var salt:int := sample();
    var key:int  := sample();
    var hash1:int := sample();
    var m:map<Tri, int>;
    // since Calculated is initially empty, the code above is identical except when the next call to Hash queries the same pwd, salt, key
    // that is, when pwd != g, the following code is identical to version 1
    // so P(r_1) <= P(pwd != g) + P(r_2) = 1/2^k + P(r_2), where k is the length of password
    
    // adverary can call HA
    var tmp_pwd, tmp_salt, tmp_key := *, *, *;
    var L:set<int> := {tmp_key};
    var r';
    r', m := Hash( Triple(tmp_pwd, tmp_salt, tmp_key), m);
    var g:int := guess(hash1, salt);
    
    var t':Tri := Triple(g, salt, key);
    var hash2:int;
    hash2, m := Hash(t', m);
    return (hash1 == hash2);
}

// version 3
method PwdBox3() returns (b:bool)
{
    var pwd:int := sample();
    var salt:int := sample();
    var key:int  := sample();
    var hash1:int := sample();
    var m:map<Tri, int>;
    // when tmp_key != key, calling HA does not affect anything
    // that is, when pwd != g && tmp_key != key, the following code is identical to version 1
    // so P(r_1) <= P(pwd != g) + P(tmp_key != key) + P(r_2) = 1/2^k + P(tmp_key != key) + P(r_2), where k is the length of password
    
    // adverary can call HA
    var g:int := guess(hash1, salt);
    
    var t':Tri := Triple(g, salt, key);
    var hash2:int;
    hash2, m := Hash(t', m);
    return (hash1 == hash2);
}

// version 4
method PwdBox4() returns (b:bool)
{
    var salt:int := sample();
    var hash1:int := sample();
    var m:map<Tri, int>;
    // since Calcuated must be empty, calling Hash(t') is the same as calling sample()
    // so P(r_1) <= 1/2^k + P(tmp_key != key) + P(r_2) = 1/2^k + 1/2^m + 1/2^n
    
    // adverary can call HA
    var g:int := guess(hash1, salt);
    var hash2:int := sample();
    var key := sample();
    var password := sample();
    return (hash1 == hash2);
}
*/

////// PwdBox-Game1

/* common declarations for Hash and sample */
ghost var global_sample_index:int;
ghost var randomSource:map<int, int>;

// these methods are defined in Entry.beat
function method word(x:int):bool
method serialPortOut (x:int)
method serialPortIn () returns (r:int)
  ensures (word(r));
method sample (ghost M:map<int, int>) returns (r:int)
  modifies this;
  ensures Hashed == old(Hashed);
  ensures randomSource[old(global_sample_index)] == r;
  ensures old(global_sample_index)+1 == global_sample_index;

function SampleVal(index:int):int

ghost method SampleLemmaID(M:map<int,int>)
  ensures (forall x :: x in M ==> M[x] == x);

ghost var Hashed:map<Tri, int>;
function RdmOracle (tri:Tri, ret:int, HashedOld:map<Tri, int>, Hashed:map<Tri, int>, index:int, randomSource:map<int, int>) : bool
{
     (tri in HashedOld ==> Hashed == HashedOld && Hashed[tri] == ret /*&& index == index+1*/) // increase the index in random source anyway
  && (!(tri in HashedOld) ==> SampleVal(index) == ret && Hashed == HashedOld[tri := ret])
}

method Hash(pwd:int, salt:int, k:int) returns (r:int)
  modifies this; 
  ensures RdmOracle(Triple(pwd, salt, k), r, old(Hashed), Hashed, old(global_sample_index), randomSource);
  ensures global_sample_index == old(global_sample_index)+1;

/* implementation */
datatype Tri = Triple(Pwd:int, Salt:int, Key:int);

method init (pwd:int, key:int) returns (hash:int, salt:int)
  modifies this;
  ensures randomSource[old(global_sample_index)] == salt;
  ensures RdmOracle(Triple(pwd, salt, key), hash, old(Hashed), Hashed, old(global_sample_index)+1, randomSource);
  ensures global_sample_index == old(global_sample_index)+2;
{
    ghost var M:map<int, int>;
    SampleLemmaID(M);
    salt := sample(M);
    hash := Hash(pwd, salt, key);
    // assert false;
} 

method verify (pwd:int, salt:int, key:int) returns (hash:int) 
  modifies this; 
  ensures RdmOracle(Triple(pwd, salt, key), hash, old(Hashed), Hashed, old(global_sample_index), randomSource);
  ensures global_sample_index == old(global_sample_index)+1;
{
    hash := Hash(pwd, salt, key);
}

/* game definition and check*/

// abstract adversary
method adversary(hash:int, salt:int) returns (guess:int, key:int)
  ensures (exists x:int, y:int, u:int :: RdmOracle(Triple(x, y, key), u, old(Hashed), Hashed, old(global_sample_index), randomSource));
{
}

method Game () returns (ghost g_hash_db:int, ghost g_hash_verify:int, ghost g_pwd:int, ghost g_key:int, ghost g_k:int)
  modifies this;
{
    ghost var M:map<int, int>;
    var pwd:int, key:int, salt:int, hash_verify:int, hash_db:int, g:int, k:int;
    SampleLemmaID(M);
    // game 2
    pwd := sample(M);
    key := sample(M);
    salt := sample(M);
    hash_db := sample(M);
    // adversary may call oracle with 
    // arbitrary values
    g, k := adversary(hash_db, salt);
    
    hash_verify := sample(M);
    // succ := (hash_db == hash_verify);
    // need to expose these variables to SymDiff
    g_hash_db := hash_db;
    g_hash_verify := hash_verify;
    g_pwd := pwd;
    g_key := key;
    g_k := k;
    //var t:Tri := Triple(g, salt, key);
    //hash2, m := Hash(t, rn6, m);
}

/*
method OpenDictSecure( ) 
      returns (perm:map<int, int>, hash_db:int, hash_verify:int, g:int, pwd:int, salt:int, h:int, adv_pwd:int, adv_salt:int, adv_key:int,
               hash_db':int, hash_verify':int, g':int, pwd':int, salt':int, key':int, h':int)
  modifies this;
  requires global_sample_index == 0;
  requires Map == map[];
  ensures ( (SampleVal(0) == SampleVal(6) && SampleVal(1) == SampleVal(7) && SampleVal(2) == SampleVal(8) && SampleVal(3) == SampleVal(9)
          && SampleVal(4) == SampleVal(10) && SampleVal(5) == SampleVal(11)) ==> 
    (pwd'!=g') && (adv_key!=key') ==> ((hash_db==hash_verify) == (hash_db'==hash_verify')));
    // Hence, we have
    //    P(hash1==hash2) 
    // <= P(hash1'==hash2') + P(tmp_key == key') + P(pwd' == g') 
    // =  1/2^n + 1/2^k + 1/2^m, where n is the length of the hash value, k the length of the key, and m is the length of the password
{
    ghost var M:map<int, int>;
    SampleLemma(M);
    // game 1
    pwd := sample(M);
    assert global_sample_index == 1;
    hash_db, salt := init(pwd);
    assert global_sample_index == 4;
    // adversary may call oracle with 
    // arbitrary values
    adv_pwd, adv_salt, adv_key  := *,*,*;
    h := Hash(adv_pwd, adv_salt, adv_key);
    assert global_sample_index == 5;
    g := guess(hash_db, salt, h);
    
    hash_verify := verify(g, salt);
    assert global_sample_index == 6;
    //var t:Tri := Triple(g, salt, key);
    //hash2, m := Hash(t, rn6, m);

    // game 2
    pwd' := sample(M);  
    key' := sample(M);  
    salt' := sample(M); 
    hash_db' := sample(M);
    h' := sample(M);    
    g' := guess(hash_db', salt', h');
    hash_verify' := sample(M);
}
*/

/*
// version 1, we want to calculate P(hash1 == hash2)
method PwdBox1() returns (b:bool)
{
    var pwd:int := sample();
    var salt:int := sample();
    var key:int  := sample();
    var t:Tri := Triple(pwd,salt,key);
    var m:map<Tri,int>;
    // version 1
    var hash1:int;
    hash1, m := Hash(t,m);
    
    // adverary can call HA
    var tmp_pwd, tmp_salt, tmp_key := *, *, *;
    var L:set<int> := {tmp_key};
    var r';
    r', m := Hash( Triple(tmp_pwd, tmp_salt, tmp_key), m);
    var g:int := guess(hash1, salt);
    
    var t':Tri := Triple(g, salt, key);
    var hash2:int;
    hash2, m := Hash(t', m);
    return (hash1 == hash2);
}

// version 2
method PwdBox2() returns (b:bool)
{
    var pwd:int := sample();
    var salt:int := sample();
    var key:int  := sample();
    var hash1:int := sample();
    var m:map<Tri, int>;
    // since Calculated is initially empty, the code above is identical except when the next call to Hash queries the same pwd, salt, key
    // that is, when pwd != g, the following code is identical to version 1
    // so P(r_1) <= P(pwd != g) + P(r_2) = 1/2^k + P(r_2), where k is the length of password
    
    // adverary can call HA
    var tmp_pwd, tmp_salt, tmp_key := *, *, *;
    var L:set<int> := {tmp_key};
    var r';
    r', m := Hash( Triple(tmp_pwd, tmp_salt, tmp_key), m);
    var g:int := guess(hash1, salt);
    
    var t':Tri := Triple(g, salt, key);
    var hash2:int;
    hash2, m := Hash(t', m);
    return (hash1 == hash2);
}

// version 3
method PwdBox3() returns (b:bool)
{
    var pwd:int := sample();
    var salt:int := sample();
    var key:int  := sample();
    var hash1:int := sample();
    var m:map<Tri, int>;
    // when tmp_key != key, calling HA does not affect anything
    // that is, when pwd != g && tmp_key != key, the following code is identical to version 1
    // so P(r_1) <= P(pwd != g) + P(tmp_key != key) + P(r_2) = 1/2^k + P(tmp_key != key) + P(r_2), where k is the length of password
    
    // adverary can call HA
    var g:int := guess(hash1, salt);
    
    var t':Tri := Triple(g, salt, key);
    var hash2:int;
    hash2, m := Hash(t', m);
    return (hash1 == hash2);
}

// version 4
method PwdBox4() returns (b:bool)
{
    var salt:int := sample();
    var hash1:int := sample();
    var m:map<Tri, int>;
    // since Calcuated must be empty, calling Hash(t') is the same as calling sample()
    // so P(r_1) <= 1/2^k + P(tmp_key != key) + P(r_2) = 1/2^k + 1/2^m + 1/2^n
    
    // adverary can call HA
    var g:int := guess(hash1, salt);
    var hash2:int := sample();
    var key := sample();
    var password := sample();
    return (hash1 == hash2);
}
*/
////// PwdBox-InOne

/* common declarations for Hash and sample */
ghost var index:int;
ghost var Map:map<Tri, int>;

method sample () returns (r:int)
  modifies this;
  ensures sampleCall (old(index), index, r);
  ensures Map == old(Map);
  ensures key == old(key);

function sampleI (i:int) :int

function sampleCall (indexOld:int, index:int, ret:int ) : bool
{
     (ret == sampleI(indexOld))
  && (index == indexOld+1)
}

function RdmOracle (tri:Tri, ret:int, MapOld:map<Tri, int>, Map:map<Tri, int>, indexOld:int, index:int) : bool
{
     (tri in MapOld ==> Map == MapOld && Map[tri] == ret && index == indexOld+1) // increase the index in random source anyway
  && (!(tri in MapOld) ==> sampleCall(indexOld, index, ret) && Map == MapOld[tri := ret])
}

method Hash(pwd:int, salt:int, k:int) returns (r:int)
  modifies this; 
  ensures key == old(key);
  ensures RdmOracle(Triple(pwd, salt, k), r, old(Map), Map, old(index), index);

/* implementation */
datatype Tri = Triple(Pwd:int, Salt:int, Key:int);
var key:int;

method init (pwd:int) returns (hash:int, salt:int)
  modifies this;
  ensures key == sampleI(old(index));
  ensures salt == sampleI(old(index)+1);
  ensures RdmOracle(Triple(pwd, salt, key), hash, old(Map), Map, old(index)+2, index);
{
    key := sample();
    salt := sample();
    hash := Hash(pwd, salt, key);
} 

method verify (pwd:int, salt:int) returns (hash:int) 
  modifies this; 
  ensures key == old(key);
  ensures RdmOracle(Triple(pwd, salt, key), hash, old(Map), Map, old(index), index);
{
    hash := Hash(pwd, salt, key);
}

/* game definition and check*/

// abstract adversary
function method guess(hash:int, salt:int, o:int):int

function Permutation(m:map<int, int>) : bool
{
   forall i:int, j:int :: i in m ==> j in m ==> i != j ==> (m[i] != m[j]) 
}

method OpenDictSecure( ) 
      returns (perm:map<int, int>, hash_db:int, hash_verify:int, g:int, pwd:int, salt:int, h:int, adv_pwd:int, adv_salt:int, adv_key:int,
               hash_db':int, hash_verify':int, g':int, pwd':int, salt':int, key':int, h':int)
  modifies this;
  requires index == 0;
  requires Map == map[];
  ensures ( Permutation(perm));
  ensures ( (forall i:int :: i in perm ==> sampleI(i) == sampleI(perm[i])) ==>
    ( (pwd'!=g') && (adv_key!=key') ==> ((hash_db==hash_verify) == (hash_db'==hash_verify'))));
    // Hence, we have
    //    P(hash1==hash2) 
    // <= P(hash1'==hash2') + P(tmp_key == key') + P(pwd' == g') 
    // =  1/2^n + 1/2^k + 1/2^m, where n is the length of the hash value, k the length of the key, and m is the length of the password
{
    /* game 1 */
    pwd := sample();
    hash_db, salt := init(pwd);

    // adversary may call oracle with 
    // arbitrary values
    adv_pwd, adv_salt, adv_key  := *,*,*;
    h := Hash(adv_pwd, adv_salt, adv_key);
    g := guess(hash_db, salt, h);
    
    hash_verify := verify(g, salt);

    //var t:Tri := Triple(g, salt, key);
    //hash2, m := Hash(t, rn6, m);

    /* game 2 */
    salt' := sample(); 
    hash_db' := sample();
    h' := sample();    
    g' := guess(hash_db', salt', h');
    pwd' := sample();  
    key' := sample();  
    hash_verify' := sample();

    perm := map[0 := 9, 1 := 10, 2 := 6, 3 := 7, 4 := 8, 5 := 11];
    // assert (false);
}

/*
// version 1, we want to calculate P(hash1 == hash2)
method PwdBox1() returns (b:bool)
{
    var pwd:int := sample();
    var salt:int := sample();
    var key:int  := sample();
    var t:Tri := Triple(pwd,salt,key);
    var m:map<Tri,int>;
    // version 1
    var hash1:int;
    hash1, m := Hash(t,m);
    
    // adverary can call HA
    var tmp_pwd, tmp_salt, tmp_key := *, *, *;
    var L:set<int> := {tmp_key};
    var r';
    r', m := Hash( Triple(tmp_pwd, tmp_salt, tmp_key), m);
    var g:int := guess(hash1, salt);
    
    var t':Tri := Triple(g, salt, key);
    var hash2:int;
    hash2, m := Hash(t', m);
    return (hash1 == hash2);
}

// version 2
method PwdBox2() returns (b:bool)
{
    var pwd:int := sample();
    var salt:int := sample();
    var key:int  := sample();
    var hash1:int := sample();
    var m:map<Tri, int>;
    // since Calculated is initially empty, the code above is identical except when the next call to Hash queries the same pwd, salt, key
    // that is, when pwd != g, the following code is identical to version 1
    // so P(r_1) <= P(pwd != g) + P(r_2) = 1/2^k + P(r_2), where k is the length of password
    
    // adverary can call HA
    var tmp_pwd, tmp_salt, tmp_key := *, *, *;
    var L:set<int> := {tmp_key};
    var r';
    r', m := Hash( Triple(tmp_pwd, tmp_salt, tmp_key), m);
    var g:int := guess(hash1, salt);
    
    var t':Tri := Triple(g, salt, key);
    var hash2:int;
    hash2, m := Hash(t', m);
    return (hash1 == hash2);
}

// version 3
method PwdBox3() returns (b:bool)
{
    var pwd:int := sample();
    var salt:int := sample();
    var key:int  := sample();
    var hash1:int := sample();
    var m:map<Tri, int>;
    // when tmp_key != key, calling HA does not affect anything
    // that is, when pwd != g && tmp_key != key, the following code is identical to version 1
    // so P(r_1) <= P(pwd != g) + P(tmp_key != key) + P(r_2) = 1/2^k + P(tmp_key != key) + P(r_2), where k is the length of password
    
    // adverary can call HA
    var g:int := guess(hash1, salt);
    
    var t':Tri := Triple(g, salt, key);
    var hash2:int;
    hash2, m := Hash(t', m);
    return (hash1 == hash2);
}

// version 4
method PwdBox4() returns (b:bool)
{
    var salt:int := sample();
    var hash1:int := sample();
    var m:map<Tri, int>;
    // since Calcuated must be empty, calling Hash(t') is the same as calling sample()
    // so P(r_1) <= 1/2^k + P(tmp_key != key) + P(r_2) = 1/2^k + 1/2^m + 1/2^n
    
    // adverary can call HA
    var g:int := guess(hash1, salt);
    var hash2:int := sample();
    var key := sample();
    var password := sample();
    return (hash1 == hash2);
}
*/
