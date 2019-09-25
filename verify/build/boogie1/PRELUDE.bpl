// *******************************************
// *                                         *
// *    Boogie Procedure Language Prelude    *
// *                                         *
// *******************************************


//------------ New types

type real;
type elements;
type struct;
type exposeVersionType;

//------------ Encode the heap

var $Heap : [ref, <x>name]x where IsHeap($Heap);
type ActivityType;
var $ActivityIndicator : ActivityType;


// IsHeap(h) holds if h is a properly formed heap
function IsHeap(h: [ref, <x>name]x) returns (bool);


// records whether a pointer refers to allocated data
const unique $allocated : <bool>name;

// the elements from dereferencing an array pointer
const unique $elements : <elements>name;
axiom DeclType($elements) == System.Object;

#if TrivialObjectModel
function $Inv(h: [ref,<x>name]x, o: ref, frame: name) returns (bool);

function $KnownClass(cl: name) returns (bool);

// System.Object class invariant
axiom (∀ $oi: ref, $h: [ref,<x>name]x • { $Inv($h, $oi, System.Object) } $Inv($h, $oi, System.Object));

// array types class invariants
axiom (∀ $oi: ref, $h: [ref,<x>name]x, T: name • { $Inv($h, $oi, T), T <: System.Array } T <: System.Array ==> $Inv($h, $oi, T));

#elsif ExperimentalObjectModel
// the name of the most derived class for which an object invariant holds
const unique $inv : <name>name;

// array, indexed by class names, that keeps a boolean showing the invariant holds for that class on the object given
const unique $validfor: <[name]bool>name;

axiom (∀ h: [ref,<x>name]x, o: ref, T: name • {h[o, $validfor][T]} 
    IsHeap(h) ∧ o ≠ null ∧  $typeof(o) <: T ∧ $BaseClass(T) <: h[o, $inv] ==> ¬h[o, $validfor][T]);
axiom (∀ h: [ref,<x>name]x, o: ref • {h[o,$inv]} 
    IsHeap(h) ∧ o ≠ null && h[o,$validfor][$typeof(o)] ==> h[o,$inv] == $typeof(o));

#else
// the name of the most derived class for which an object invariant holds
const unique $inv : <name>name;

// the name of (the supertype of) the class for which the object invariant is allowed to be broken
const unique $localinv: <name>name;

#endif

// dummy field that is havoced at unpacks so that it can be used to deduce state changes  
const unique $exposeVersion : <exposeVersionType>name;

// declaration type of exposeVersion is System.Object
axiom DeclType($exposeVersion) == System.Object;

#if !TrivialObjectModel
// the $sharingMode field indicates the object's sharing mode, which is either $SharingMode_Unshared or $SharingMode_LockProtected
const unique $sharingMode : name;
const unique $SharingMode_Unshared : name;
const unique $SharingMode_LockProtected : name;

// a reference to the object ($ownerRef, $ownerFrame)
const unique $ownerRef : <ref>name;
const unique $ownerFrame : <name>name;
const unique $PeerGroupPlaceholder : name;  // used as a type name
#endif

// a map from class names to their representative "references" used to obtain values of static fields
function ClassRepr(class: name) returns (ref);
// this map is injective
function ClassReprInv(ref) returns (name);
axiom (∀ c: name • {ClassRepr(c)} ClassReprInv(ClassRepr(c)) == c);
axiom (∀ T:name • ¬($typeof(ClassRepr(T)) <: System.Object));
axiom (∀ T:name • ClassRepr(T) ≠ null);
#if !TrivialObjectModel
axiom (∀ T:name, h:[ref,<x>name]x • {h[ClassRepr(T),$ownerFrame]} IsHeap(h) ⇒ h[ClassRepr(T),$ownerFrame] == $PeerGroupPlaceholder);
#endif

//------------ Fields
// fields are classified into whether or not the field is static (i.e., it is a field of a ClassRepr "ref") 
// and whether or not it is directly modifiable by the user

// indicates a field has to be part of the frame condition
function IncludeInMainFrameCondition(f:name) returns (bool);
axiom IncludeInMainFrameCondition($allocated);
axiom IncludeInMainFrameCondition($elements);
#if !TrivialObjectModel
axiom ¬(IncludeInMainFrameCondition($inv));
#if ExperimentalObjectModel
axiom ¬(IncludeInMainFrameCondition($validfor));
#else
axiom ¬(IncludeInMainFrameCondition($localinv));
#endif
axiom IncludeInMainFrameCondition($ownerRef);
axiom IncludeInMainFrameCondition($ownerFrame);
#endif
axiom IncludeInMainFrameCondition($exposeVersion);
#if !TrivialObjectModel
axiom ¬(IncludeInMainFrameCondition($FirstConsistentOwner));
#endif

// indicates a field is static
function IsStaticField(f: name) returns (bool);
axiom ¬IsStaticField($allocated);
axiom ¬IsStaticField($elements);
#if !TrivialObjectModel
axiom ¬IsStaticField($inv);
#if ExperimentalObjectModel
axiom ¬IsStaticField($validfor);
#else
axiom ¬IsStaticField($localinv);
#endif
#endif
axiom ¬IsStaticField($exposeVersion);

// indicates if a is included in modifies o.* and o.**
function $IncludedInModifiesStar(f: name) returns (bool);
#if !TrivialObjectModel
axiom ¬$IncludedInModifiesStar($ownerRef);
axiom ¬$IncludedInModifiesStar($ownerFrame);
#endif
// $inv and $localinv are not included either, but we don't need to say that in an axiom
// the same for $validfor
axiom $IncludedInModifiesStar($exposeVersion);
axiom $IncludedInModifiesStar($elements);


//------------ Array elements

function ValueArrayGet (elements, int) returns (any);
function ValueArraySet (elements, int, any) returns (elements);
function IntArrayGet (elements, int) returns (int);
function IntArraySet (elements, int, int) returns (elements);
function RefArrayGet (elements, int) returns (ref);
function RefArraySet (elements, int, ref) returns (elements);

axiom (∀ A:elements, i:int, x:any • ValueArrayGet(ValueArraySet(A, i, x), i) == x);
axiom (∀ A:elements, i:int, j:int, x:any • i ≠ j  ⇒ ValueArrayGet(ValueArraySet(A, i, x), j) == ValueArrayGet(A, j)); 
axiom (∀ A:elements, i:int, x:int • IntArrayGet(IntArraySet(A, i, x), i) == x);
axiom (∀ A:elements, i:int, j:int, x:int • i ≠ j  ⇒ IntArrayGet(IntArraySet(A, i, x), j) == IntArrayGet(A, j)); 
axiom (∀ A:elements, i:int, x:ref • RefArrayGet(RefArraySet(A, i, x), i) == x);
axiom (∀ A:elements, i:int, j:int, x:ref • i ≠ j  ⇒ RefArrayGet(RefArraySet(A, i, x), j) == RefArrayGet(A, j)); 

// the indices of multi-dimensional arrays are built up one dimension at a time
function ArrayIndex(arr: ref, dim: int, indexAtDim: int, remainingIndexContribution: int) returns (int);
// the expressions built up are injective in the indices
function ArrayIndexInvX(arrayIndex: int) returns (indexAtDim: int);
function ArrayIndexInvY(arrayIndex: int) returns (remainingIndexContribution: int);
axiom (∀ a:ref, d:int, x: int, y: int •  {ArrayIndex(a,d,x,y)}  ArrayIndexInvX(ArrayIndex(a,d,x,y)) == x);
axiom (∀ a:ref, d:int, x: int, y: int •  {ArrayIndex(a,d,x,y)}  ArrayIndexInvY(ArrayIndex(a,d,x,y)) == y);

axiom (∀ a:ref, i:int, heap:[ref,<x>name]x •
   { IntArrayGet(heap[a, $elements], i) }
   IsHeap(heap) ⇒  InRange(IntArrayGet(heap[a, $elements], i), $ElementType($typeof(a))));
axiom (∀ a:ref, i:int, heap:[ref,<x>name]x •
    { $typeof(RefArrayGet(heap[a, $elements], i)) }
    IsHeap(heap) ∧ RefArrayGet(heap[a, $elements], i) ≠ null  ⇒
    $typeof(RefArrayGet(heap[a, $elements], i)) <: $ElementType($typeof(a)));
axiom (∀ a:ref, T:name, i:int, r:int, heap:[ref,<x>name]x •
    { $typeof(a) <: NonNullRefArray(T, r), RefArrayGet(heap[a, $elements], i) }
    IsHeap(heap) ∧ $typeof(a) <: NonNullRefArray(T,r)  ⇒  RefArrayGet(heap[a, $elements], i) ≠ null);

//------------ Array properties: rank, length, dimensions, upper and lower bounds

function $Rank (ref) returns (int); 
axiom (∀ a:ref • 1 ≤ $Rank(a));
axiom (∀ a:ref, T:name, r:int • {$typeof(a) <: RefArray(T,r)} a ≠ null ∧ $typeof(a) <: RefArray(T,r)  ⇒ $Rank(a) == r);
axiom (∀ a:ref, T:name, r:int • {$typeof(a) <: NonNullRefArray(T,r)} a ≠ null ∧ $typeof(a) <: NonNullRefArray(T,r)  ⇒ $Rank(a) == r);
axiom (∀ a:ref, T:name, r:int • {$typeof(a) <: ValueArray(T,r)} a ≠ null ∧ $typeof(a) <: ValueArray(T,r)  ⇒ $Rank(a) == r);
axiom (∀ a:ref, T:name, r:int • {$typeof(a) <: IntArray(T,r)} a ≠ null ∧ $typeof(a) <: IntArray(T,r)  ⇒ $Rank(a) == r);

function $Length (ref) returns (int);
axiom (∀ a:ref • {$Length(a)} 0 ≤ $Length(a) ∧ $Length(a) ≤ int#2147483647);

function $DimLength (ref, int) returns (int); // length per dimension up to rank
axiom (∀ a:ref, i:int • 0 ≤ $DimLength(a,i));
// The trigger used in the following axiom is restrictive, so that this disjunction is not
// produced too easily.  Is the trigger perhaps sometimes too restrictive?
axiom (∀ a:ref • { $DimLength(a,0) }  $Rank(a) == 1 ⇒ $DimLength(a,0) == $Length(a));

function $LBound (ref, int) returns (int); 
function $UBound (ref, int) returns (int);
// Right now we only model C# arrays:
axiom (∀ a:ref, i:int • {$LBound(a,i)} $LBound(a,i) == 0);
axiom (∀ a:ref, i:int • {$UBound(a,i)} $UBound(a,i) == $DimLength(a,i)-1);

// Different categories of arrays are different types

const unique $ArrayCategoryValue: name;
const unique $ArrayCategoryInt: name;
const unique $ArrayCategoryRef: name;
const unique $ArrayCategoryNonNullRef: name;

function $ArrayCategory(arrayType: name) returns (arrayCategory: name);

axiom (∀ T: name, ET: name, r: int • { T <: ValueArray(ET, r) } T <: ValueArray(ET, r) ⇒ $ArrayCategory(T) == $ArrayCategoryValue);
axiom (∀ T: name, ET: name, r: int • { T <: IntArray(ET, r) } T <: IntArray(ET, r) ⇒ $ArrayCategory(T) == $ArrayCategoryInt);
axiom (∀ T: name, ET: name, r: int • { T <: RefArray(ET, r) } T <: RefArray(ET, r) ⇒ $ArrayCategory(T) == $ArrayCategoryRef);
axiom (∀ T: name, ET: name, r: int • { T <: NonNullRefArray(ET, r) } T <: NonNullRefArray(ET, r) ⇒ $ArrayCategory(T) == $ArrayCategoryNonNullRef);

//------------ Array types

const unique System.Array : name;
axiom System.Array <: System.Object;

function $ElementType(name) returns (name);

function ValueArray (elementType:name, rank:int) returns (name); 
axiom (∀ T:name, r:int • {ValueArray(T,r)} ValueArray(T,r) <: ValueArray(T,r) ∧ ValueArray(T,r) <: System.Array);
function IntArray (elementType:name, rank:int) returns (name); 
axiom (∀ T:name, r:int • {IntArray(T,r)} IntArray(T,r) <: IntArray(T,r) ∧ IntArray(T,r) <: System.Array);

function RefArray (elementType:name, rank:int) returns (name); 
axiom (∀ T:name, r:int • {RefArray(T,r)} RefArray(T,r) <: RefArray(T,r) ∧ RefArray(T,r) <: System.Array);
function NonNullRefArray (elementType:name, rank:int) returns (name); 
axiom (∀ T:name, r:int • {NonNullRefArray(T,r)} NonNullRefArray(T,r) <: NonNullRefArray(T,r) ∧ NonNullRefArray(T,r) <: System.Array);
function NonNullRefArrayRaw(array: ref, elementType: name, rank: int) returns (bool);
axiom (∀ array: ref, elementType: name, rank: int •  { NonNullRefArrayRaw(array, elementType, rank) }
  NonNullRefArrayRaw(array, elementType, rank)
  ⇒  $typeof(array) <: System.Array ∧ $Rank(array) == rank ∧ elementType <: $ElementType($typeof(array)));

// arrays of references are co-variant
axiom (∀ T:name, U:name, r:int • U <: T  ⇒  RefArray(U,r) <: RefArray(T,r));
axiom (∀ T:name, U:name, r:int • U <: T  ⇒  NonNullRefArray(U,r) <: NonNullRefArray(T,r));

axiom (∀ A: name, r: int • $ElementType(ValueArray(A,r)) == A);
axiom (∀ A: name, r: int • $ElementType(IntArray(A,r)) == A);
axiom (∀ A: name, r: int • $ElementType(RefArray(A,r)) == A);
axiom (∀ A: name, r: int • $ElementType(NonNullRefArray(A,r)) == A);

// subtypes of array types
axiom (∀ A: name, r: int, T: name •  {T <: RefArray(A,r)} T <: RefArray(A,r)  ⇒  T ≠ A ∧ T == RefArray($ElementType(T),r) ∧ $ElementType(T) <: A);
axiom (∀ A: name, r: int, T: name •  {T <: NonNullRefArray(A,r)} T <: NonNullRefArray(A,r)  ⇒  T ≠ A ∧ T == NonNullRefArray($ElementType(T),r) ∧ $ElementType(T) <: A);
axiom (∀ A: name, r: int, T: name •  {T <: ValueArray(A, r)} T <: ValueArray(A, r)  ⇒  T == ValueArray(A, r));
axiom (∀ A: name, r: int, T: name •  {T <: IntArray(A, r)} T <: IntArray(A, r)  ⇒  T == IntArray(A, r));

// supertypes of array types
axiom (∀ A: name, r: int, T: name •  {RefArray(A,r) <: T}  RefArray(A,r) <: T  ⇒  System.Array <: T ∨ (T == RefArray($ElementType(T),r) ∧ A <: $ElementType(T)));
axiom (∀ A: name, r: int, T: name •  {NonNullRefArray(A,r) <: T}  NonNullRefArray(A,r) <: T  ⇒  System.Array <: T ∨ (T == NonNullRefArray($ElementType(T),r) ∧ A <: $ElementType(T)));
axiom (∀ A: name, r: int, T: name •  {ValueArray(A, r) <: T}  ValueArray(A, r) <: T  ⇒  System.Array <: T ∨ T == ValueArray(A, r));
axiom (∀ A: name, r: int, T: name •  {IntArray(A, r) <: T}  IntArray(A, r) <: T  ⇒  System.Array <: T ∨ T == IntArray(A, r));

function $ArrayPtr (elementType:name) returns (name); 


//------------ Array and generic element ownership
function $ElementProxy(ref, int) returns (ref);
function $ElementProxyStruct(struct, int) returns (ref);


#if !TrivialObjectModel
axiom (∀ a: ref, i: int, heap: [ref,<x>name]x :: { heap[RefArrayGet(heap[a, $elements], i),$ownerRef] } { heap[RefArrayGet(heap[a, $elements], i),$ownerFrame] } IsHeap(heap) ∧ $typeof(a) <: System.Array ⇒ RefArrayGet(heap[a, $elements], i) == null ∨ $IsImmutable($typeof(RefArrayGet(heap[a, $elements], i))) ∨ (heap[RefArrayGet(heap[a, $elements], i),$ownerRef] == heap[$ElementProxy(a,-1),$ownerRef] ∧ heap[RefArrayGet(heap[a, $elements], i),$ownerFrame] == heap[$ElementProxy(a,-1),$ownerFrame]));
#endif

axiom (∀ a: ref, heap: [ref,<x>name]x :: { IsAllocated(heap,a) } IsHeap(heap) ∧ IsAllocated(heap,a) ∧ $typeof(a) <: System.Array ⇒ IsAllocated(heap, $ElementProxy(a,-1)));

axiom (∀ o: ref, pos: int :: { $typeof($ElementProxy(o,pos)) } $typeof($ElementProxy(o,pos)) == System.Object);
axiom (∀ o: struct, pos: int :: { $typeof($ElementProxyStruct(o,pos)) } $typeof($ElementProxyStruct(o,pos)) == System.Object);


//------------ Encode structs

function $StructGet (struct, name) returns (any);

function $StructSet (struct, name, any) returns (struct);


axiom (∀ s:struct, f:name, x:any • $StructGet($StructSet(s, f, x), f) == x);
		
axiom (∀ s:struct, f:name, f':name, x:any • f ≠ f'  ⇒  $StructGet($StructSet(s, f, x), f') == $StructGet(s, f')); 

function ZeroInit(s:struct, typ:name) returns (bool);
// TODO: ZeroInit needs axiomatization that says the fields of s are 0 or null or ZeroInit, depending on their types


//------------ Encode type information

function $typeof (ref) returns (name);

function $BaseClass(sub: name) returns (base: name);
axiom (∀ T: name •  { $BaseClass(T) }  T <: $BaseClass(T) ∧  (T != System.Object ==> T != $BaseClass(T)));

// Incomparable subtype axiom:
function AsDirectSubClass(sub: name, base: name) returns (sub': name);
function OneClassDown(sub: name, base: name) returns (directSub: name);
axiom (∀ A: name, B: name, C: name • { C <: AsDirectSubClass(B,A) }  C <: AsDirectSubClass(B,A)  ⇒  OneClassDown(C,A) == B);

// primitive types are unordered in the type ordering
function $IsValueType(name) returns (bool);
axiom (∀ T: name • $IsValueType(T)  ⇒  (∀ U: name •  T <: U  ⇒  T == U) ∧ (∀ U: name •  U <: T  ⇒  T == U));

const unique System.Boolean: name;  // bool
axiom $IsValueType(System.Boolean);

// type constructor T[] 
//
const unique System.Object : name;

// reflection
//
function $IsTokenForType (struct, name) returns (bool);
function TypeObject (name) returns (ref); // Corresponds with C# typeof(T)
const unique System.Type : name;
axiom System.Type <: System.Object;
axiom (∀ T:name • {TypeObject(T)} $IsNotNull(TypeObject(T), System.Type));
function TypeName(ref) returns (name);  // the inverse of TypeObject, which is injective
axiom (∀ T:name • {TypeObject(T)}  TypeName(TypeObject(T)) == T);

function $Is (ref, name) returns (bool);
axiom (∀ o:ref, T:name • {$Is(o, T)} $Is(o, T)  ⇔  o == null ∨ $typeof(o) <: T);

function $IsNotNull(ref, name) returns (bool);
axiom (∀ o:ref, T:name • {$IsNotNull(o, T)} $IsNotNull(o, T)  ⇔  o ≠ null ∧ $Is(o,T));

// $As(o,T) is to be used only when T denotes a reference type (see also BoxTester).  It returns either o or null.
function $As (ref, name) returns (ref);
axiom (∀ o:ref, T:name • $Is(o, T)  ⇒  $As(o, T) == o);
axiom (∀ o:ref, T:name • ¬ $Is(o, T)  ⇒  $As(o, T) == null);

// Arrays are always valid (but may be committed)
#if ExperimentalObjectModel
axiom (∀ o: ref • {$typeof(o) <: System.Array} o ≠ null ∧ $typeof(o) <: System.Array  ⇒ 
         (∀ h: [ref,<x>name]x • {h[o,$inv]} {h[o,$validfor]} IsHeap(h) ⇒  
            (∀ T: name • {h[o,$validfor][T]} h[o,$validfor][T]) ∧ 
            h[o,$inv] == $typeof(o)));
#elsif !TrivialObjectModel
axiom (∀ h: [ref,<x>name]x, o: ref • {$typeof(o) <: System.Array, h[o,$inv]} IsHeap(h) ∧ o ≠ null ∧ $typeof(o) <: System.Array  ⇒  h[o,$inv] == $typeof(o) ∧ h[o,$localinv] == $typeof(o));
#endif

//---------- Types and allocation of reachable things

function IsAllocated(h: [ref,<x>name]x, o: any) returns (bool);

// everything in the range of a proper heap is allocated whenever the domain is
axiom (∀ h: [ref,<x>name]x, o: ref, f: name • {IsAllocated(h, h[o,f])} IsHeap(h) ∧ h[o, $allocated]  ⇒  IsAllocated(h, h[o,f]));
axiom (∀ h: [ref,<x>name]x, o: ref, f: <ref>name • {h[h[o,f], $allocated]} IsHeap(h) ∧ h[o, $allocated]  ⇒  h[h[o,f], $allocated]);

axiom (∀ h: [ref,<x>name]x, s: struct, f: name • {IsAllocated(h, $StructGet(s,f))} IsAllocated(h,s)  ⇒  IsAllocated(h, $StructGet(s,f)));
axiom (∀ h: [ref,<x>name]x, e: elements, i: int• {IsAllocated(h, RefArrayGet(e,i))} IsAllocated(h,e)  ⇒  IsAllocated(h, RefArrayGet(e,i)));
axiom (∀ h: [ref,<x>name]x, e: elements, i: int• {IsAllocated(h, ValueArrayGet(e,i))} IsAllocated(h,e)  ⇒  IsAllocated(h, ValueArrayGet(e,i)));
// no need to have IsAllocated for IntArray's

axiom (∀ h: [ref,<x>name]x, o: ref • {h[o, $allocated]}  IsAllocated(h,o)  ⇒  h[o, $allocated]);

axiom (∀ h: [ref,<x>name]x, c:name • {h[ClassRepr(c), $allocated]} IsHeap(h)  ⇒  h[ClassRepr(c), $allocated]);

const $BeingConstructed: ref;
const unique $NonNullFieldsAreInitialized: <bool>name;
const $PurityAxiomsCanBeAssumed: bool;
axiom DeclType($NonNullFieldsAreInitialized) == System.Object;

// types of fields
function DeclType(field: name) returns (class: name);  // for "class C { T f; ...", DeclType(f) == C
function AsNonNullRefField(field: <ref>name, T: name) returns (f: <ref>name);  // for "class C { T! f; ...", AsNonNullRefField(f,T) == f
function AsRefField(field: <ref>name, T: name) returns (f: <ref>name);  // for "class C { T f; ...", AsRefField(f,T) == f
// for integral types T
function AsRangeField(field: <int>name, T: name) returns (f: <int>name);  // for "class C { T f; ...", AsRangeField(f,T) == f

axiom (∀ f: <ref>name, T: name • {AsNonNullRefField(f,T)}  AsNonNullRefField(f,T)==f  ⇒  AsRefField(f,T)==f);

// fields in the heap are well typed
axiom (∀ h: [ref,<x>name]x, o: ref, f: <ref>name, T: name • {h[o,AsRefField(f,T)]}  IsHeap(h)  ⇒  $Is(h[o,AsRefField(f,T)], T));
axiom (∀ h: [ref,<x>name]x, o: ref, f: <ref>name, T: name • {h[o,AsNonNullRefField(f,T)]}  IsHeap(h) ∧ o ≠ null ∧ (o ≠ $BeingConstructed ∨ h[$BeingConstructed, $NonNullFieldsAreInitialized] == true) ⇒  h[o,AsNonNullRefField(f,T)] ≠ null);
axiom (∀ h: [ref,<x>name]x, o: ref, f: <int>name, T: name • {h[o,AsRangeField(f,T)]}  IsHeap(h)  ⇒  InRange(h[o,AsRangeField(f,T)], T));

// abstract classes, interfaces, ...
function $IsMemberlessType(name) returns (bool);
axiom (∀ o: ref • { $IsMemberlessType($typeof(o)) }  ¬$IsMemberlessType($typeof(o)));
function $AsInterface(name) returns (name);
// this axiom relates a boxed struct to any interfaces that the struct implements
// otherwise, all that is known is that a boxed struct is of type System.Object which isn't strong enough
axiom (∀ $J: name, s: any, b: ref • { UnboxedType(Box(s,b)) <: $AsInterface($J) } $AsInterface($J) == $J && Box(s,b)==b && UnboxedType(Box(s,b)) <: $AsInterface($J) ==> $typeof(b) <: $J);

function $HeapSucc(oldHeap: [ref, <x>name]x, newHeap: [ref, <x>name]x) returns (bool);

//------------ Immutable types

function $IsImmutable(T:name) returns (bool);

// We say here that System.Object is mutable, but only using the $IsImmutable predicate.  The functions
// $AsImmutable and $AsMutable below are used to say that all subtypes below fixpoints of these functions
// are also fixpoints.
axiom !$IsImmutable(System.Object);

function $AsImmutable(T:name) returns (theType: name);
function $AsMutable(T:name) returns (theType: name);

axiom (∀ T: name, U:name • {U <: $AsImmutable(T)} U <: $AsImmutable(T) ⇒  $IsImmutable(U) ∧ $AsImmutable(U) == U);
axiom (∀ T: name, U:name • {U <: $AsMutable(T)} U <: $AsMutable(T) ⇒  !$IsImmutable(U) ∧ $AsMutable(U) == U);

function AsOwner(string: ref, owner: ref) returns (theString: ref);

#if ExperimentalObjectModel
axiom (∀ o: ref , T:name • {$typeof(o) <: $AsImmutable(T)}
    o ≠ null ∧ o ≠ $BeingConstructed  ∧ $typeof(o) <: $AsImmutable(T)
    ⇒ 
    (∀ h: [ref,<x>name]x • {IsHeap(h)}
        IsHeap(h)
        ⇒
        (∀ S:name • h[o,$validfor][S]) ∧
        h[o, $inv] == $typeof(o) ∧
        h[o, $ownerFrame] == $PeerGroupPlaceholder ∧
        AsOwner(o, h[o, $ownerRef]) == o ∧
        (∀ t: ref •  {AsOwner(o, h[t, $ownerRef])}
            AsOwner(o, h[t, $ownerRef]) == o
            ⇒
            t == o  ∨  h[t, $ownerFrame] ≠ $PeerGroupPlaceholder)));
#elsif !TrivialObjectModel
axiom (∀ o: ref , T:name • {$typeof(o) <: $AsImmutable(T)}
    o ≠ null ∧ o ≠ $BeingConstructed  ∧ $typeof(o) <: $AsImmutable(T)
    ⇒ 
    (∀ h: [ref,<x>name]x • {IsHeap(h)}
        IsHeap(h)
        ⇒
        h[o, $inv] == $typeof(o) ∧ h[o, $localinv] == $typeof(o) ∧
        h[o, $ownerFrame] == $PeerGroupPlaceholder ∧
        AsOwner(o, h[o, $ownerRef]) == o ∧
        (∀ t: ref •  {AsOwner(o, h[t, $ownerRef])}
            AsOwner(o, h[t, $ownerRef]) == o
            ⇒
            t == o  ∨  h[t, $ownerFrame] ≠ $PeerGroupPlaceholder)));
#endif

//------------ Encode methodology

const unique System.String: name;

function $StringLength (ref) returns (int);
axiom (∀ s:ref • {$StringLength(s)} 0 ≤ $StringLength(s));

// for rep fields
function AsRepField(f: <ref>name, declaringType: name) returns (theField: <ref>name);

#if !TrivialObjectModel
axiom (∀ h: [ref,<x>name]x, o: ref, f: <ref>name, T: name  •  {h[o,AsRepField(f,T)]}  IsHeap(h) ∧ h[o,AsRepField(f,T)] ≠ null  ⇒  h[h[o,AsRepField(f,T)], $ownerRef] == o ∧ h[h[o,AsRepField(f,T)], $ownerFrame] == T);
#endif

// for peer fields
function AsPeerField(f: <ref>name) returns (theField: <ref>name);

#if !TrivialObjectModel
axiom (∀ h: [ref,<x>name]x, o: ref, f: <ref>name  •  {h[o,AsPeerField(f)]}  IsHeap(h) ∧ h[o,AsPeerField(f)] ≠ null  ⇒  h[h[o,AsPeerField(f)], $ownerRef] == h[o, $ownerRef] ∧ h[h[o,AsPeerField(f)], $ownerFrame] == h[o, $ownerFrame]);
#endif

// for ElementsRep fields
function AsElementsRepField(f: <ref>name, declaringType: name, position: int) returns (theField: <ref>name);

#if !TrivialObjectModel
axiom (∀ h: [ref,<x>name]x, o: ref, f: <ref>name, T: name, i: int  •  {h[o,AsElementsRepField(f,T,i)]}  IsHeap(h) ∧ h[o,AsElementsRepField(f,T,i)] ≠ null  ⇒  h[$ElementProxy(h[o,AsElementsRepField(f,T,i)],i), $ownerRef] == o ∧ h[$ElementProxy(h[o,AsElementsRepField(f,T,i)],i), $ownerFrame] == T);
#endif

// for ElementsPeer fields
function AsElementsPeerField(f: <ref>name, position: int) returns (theField: <ref>name);

#if !TrivialObjectModel
axiom (∀ h: [ref,<x>name]x, o: ref, f: <ref>name, i: int  •  {h[o,AsElementsPeerField(f,i)]}  IsHeap(h) ∧ h[o,AsElementsPeerField(f,i)] ≠ null  ⇒  h[$ElementProxy(h[o,AsElementsPeerField(f,i)],i), $ownerRef] == h[o, $ownerRef] ∧ h[$ElementProxy(h[o,AsElementsPeerField(f,i)],i), $ownerFrame] == h[o, $ownerFrame]);
#endif



// committed fields are fully valid
#if ExperimentalObjectModel
// this mimics what was here before, alternative: move the inner quantification
// to the outer quantification and add "h[o,$validfor][T]" to the trigger as a multi-trigger
// the above is actually the current encoding!

//axiom (∀ h:[ref,<x>name]x, o:ref •  {h[h[o,$ownerRef], $validfor][h[o, $ownerFrame]] }  
//   IsHeap(h) ∧ h[o,$ownerFrame] ≠ $PeerGroupPlaceholder ∧ h[h[o,$ownerRef],$validfor][h[o, $ownerFrame]] ⇒  
//   (∀ T:name • {h[o,$validfor][T]} h[o,$validfor][T]) ∧ h[o, $inv] == $typeof(o));

//axiom (forall h:[ref,<x>name]x, o:ref ::  {h[h[o,$ownerRef], $validfor][h[o, $ownerFrame]]} {h[o,$validfor]}  
//   IsHeap(h) && h[o,$ownerFrame] != $PeerGroupPlaceholder && h[h[o,$ownerRef],$validfor][h[o, $ownerFrame]] ==>  
//   (forall T:name :: {h[o,$validfor][T]} h[o,$validfor][T]) && h[o, $inv] == $typeof(o));

axiom (∀ h:[ref,<x>name]x, o:ref, T:name • {h[o,$validfor][T]}   
  IsHeap(h) ∧ h[o,$ownerFrame] ≠ $PeerGroupPlaceholder ∧ h[h[o,$ownerRef],$validfor][h[o, $ownerFrame]] ==>  
   h[o,$validfor][T] ∧ h[o, $inv] == $typeof(o));

// This axiom might help with some triggering of the one above, further tests needed!
axiom (∀ h:[ref,<x>name]x, o:ref • {h[o, $inv]}   
  IsHeap(h) ∧ h[o,$ownerFrame] ≠ $PeerGroupPlaceholder ∧ h[h[o,$ownerRef],$validfor][h[o, $ownerFrame]] ==>  
   h[o, $inv] == $typeof(o));

#elsif !TrivialObjectModel
axiom (∀ h:[ref,<x>name]x, o:ref  •  {h[h[o,$ownerRef], $inv] <: h[o, $ownerFrame] }  
   IsHeap(h) ∧ h[o,$ownerFrame] ≠ $PeerGroupPlaceholder ∧ h[h[o,$ownerRef], $inv] <: h[o, $ownerFrame]  ∧ h[h[o,$ownerRef], $localinv] ≠ $BaseClass(h[o, $ownerFrame])  ⇒  
   h[o,$inv] == $typeof(o) ∧ h[o,$localinv] == $typeof(o));

#endif

// The following procedure sets the owner of o and all its peers to (ow,fr).
// It expects o != null && o.$ownerFrame==$PeerGroupPlaceholder, but this condition is checked at the call site.
procedure $SetOwner(o: ref, ow: ref, fr: name);
#if !TrivialObjectModel
  modifies $Heap;
  ensures (∀ p: ref, F: name  •
      { $Heap[p, F] }
      (F ≠ $ownerRef ∧ F ≠ $ownerFrame) ∨
      old($Heap[p, $ownerRef] ≠ $Heap[o, $ownerRef]) ∨
      old($Heap[p, $ownerFrame] ≠ $Heap[o, $ownerFrame])
      ⇒  old($Heap[p, F]) == $Heap[p, F]);
  ensures (∀ p: ref  •
      { $Heap[p, $ownerRef] }
      { $Heap[p, $ownerFrame] }
      old($Heap[p, $ownerRef] == $Heap[o, $ownerRef]) ∧
      old($Heap[p, $ownerFrame] == $Heap[o, $ownerFrame])
      ⇒  $Heap[p, $ownerRef] == ow  ∧  $Heap[p, $ownerFrame] == fr);
  free ensures $HeapSucc(old($Heap), $Heap);
#endif

// The following procedure is called for "o.f = e;" where f is a rep field declared in a class T:
procedure $UpdateOwnersForRep(o: ref, T: name, e: ref);
#if !TrivialObjectModel
  modifies $Heap;
  ensures (∀ p: ref, F: name  •
      { $Heap[p, F] }
      (F ≠ $ownerRef ∧ F ≠ $ownerFrame) ∨
      old($Heap[p, $ownerRef] ≠ $Heap[e, $ownerRef]) ∨
      old($Heap[p, $ownerFrame] ≠ $Heap[e, $ownerFrame])
      ⇒  old($Heap[p, F]) == $Heap[p, F]);
  ensures e == null  ⇒  $Heap == old($Heap);
  ensures e ≠ null  ⇒  (∀ p: ref  •
      { $Heap[p, $ownerRef] }
      { $Heap[p, $ownerFrame] }
      old($Heap[p, $ownerRef] == $Heap[e, $ownerRef]) ∧
      old($Heap[p, $ownerFrame] == $Heap[e, $ownerFrame])
      ⇒  $Heap[p, $ownerRef] == o  ∧  $Heap[p, $ownerFrame] == T);
  free ensures $HeapSucc(old($Heap), $Heap);
#endif

// The following procedure is called for "c.f = d;" where f is a peer field:
procedure $UpdateOwnersForPeer(c: ref, d: ref);
#if !TrivialObjectModel
  modifies $Heap;
  ensures (∀ p: ref, F: name  •
      { $Heap[p, F] }
      (F ≠ $ownerRef ∧ F ≠ $ownerFrame) ∨
      old($Heap[p, $ownerRef] ≠ $Heap[d, $ownerRef] ∨ $Heap[p, $ownerFrame] ≠ $Heap[d, $ownerFrame])
      ⇒  old($Heap[p, F]) == $Heap[p, F]);
  ensures d == null  ⇒  $Heap == old($Heap);
  ensures d ≠ null  ⇒  (∀ p: ref  •
      { $Heap[p, $ownerRef] }
      { $Heap[p, $ownerFrame] }
      old($Heap[p, $ownerRef] == $Heap[d, $ownerRef] ∧ $Heap[p, $ownerFrame] == $Heap[d, $ownerFrame])
      ⇒
      $Heap[p, $ownerRef] == old($Heap)[c, $ownerRef] ∧
      $Heap[p, $ownerFrame] == old($Heap)[c, $ownerFrame]);
  free ensures $HeapSucc(old($Heap), $Heap);
#endif


#if !TrivialObjectModel
// Intuitively, the $FirstConsistentOwner field of an object is defined as the closest
// transitive owner that is consistent.  The field is defined if the object is committed.

const unique $FirstConsistentOwner: <ref>name;
#endif

function $AsPureObject(ref) returns (ref);  // used only for triggering
function ##FieldDependsOnFCO(o: ref, f: name, ev: exposeVersionType) returns (value: any);

#if !TrivialObjectModel
// The following axiom say that for any committed object o, each field of o is determined
// by the exposeVersion of o's first consistent owner.

#if FCOAxiom_None
#elsif FCOAxiom_ExposeVersion_Only
axiom (∀ o: ref, h: [ref,<x>name]x  •
  { h[$AsPureObject(o), $exposeVersion] }
  IsHeap(h) ∧
  o ≠ null ∧ h[o, $allocated] == true ∧ $AsPureObject(o) == o ∧
  h[o, $ownerFrame] ≠ $PeerGroupPlaceholder ∧ 
#if ExperimentalObjectModel
  h[h[o,$ownerRef],$validfor][h[o, $ownerFrame]] 
#else
  h[h[o, $ownerRef], $inv] <: h[o, $ownerFrame] ∧
  h[h[o, $ownerRef], $localinv] ≠ $BaseClass(h[o, $ownerFrame])
#endif
  ⇒
  h[o, $exposeVersion] == ##FieldDependsOnFCO(o, $exposeVersion, h[h[o, $FirstConsistentOwner], $exposeVersion]));
#else
axiom (∀ o: ref, f: name, h: [ref,<x>name]x  •
  { h[$AsPureObject(o), f] }
  IsHeap(h) ∧
  o ≠ null ∧ h[o, $allocated] == true ∧ $AsPureObject(o) == o ∧
  h[o, $ownerFrame] ≠ $PeerGroupPlaceholder ∧ 
#if ExperimentalObjectModel
  h[h[o,$ownerRef],$validfor][h[o, $ownerFrame]] 
#else
  h[h[o, $ownerRef], $inv] <: h[o, $ownerFrame] ∧
  h[h[o, $ownerRef], $localinv] ≠ $BaseClass(h[o, $ownerFrame])
#endif
  ⇒
  h[o, f] == ##FieldDependsOnFCO(o, f, h[h[o, $FirstConsistentOwner], $exposeVersion]));
#endif

axiom (∀ o: ref, h: [ref,<x>name]x  •
  { h[o, $FirstConsistentOwner] }
  IsHeap(h) ∧
  o ≠ null ∧ h[o, $allocated] == true ∧
  h[o, $ownerFrame] ≠ $PeerGroupPlaceholder ∧ 
#if ExperimentalObjectModel
  h[h[o,$ownerRef],$validfor][h[o, $ownerFrame]] 
#else
  h[h[o, $ownerRef], $inv] <: h[o, $ownerFrame] ∧
  h[h[o, $ownerRef], $localinv] ≠ $BaseClass(h[o, $ownerFrame])
#endif
  ⇒
  h[o, $FirstConsistentOwner] != null ∧
  h[h[o, $FirstConsistentOwner], $allocated] == true ∧
  // ¬ h[h[o, $FirstConsistentOwner], Committed]
  (h[h[o, $FirstConsistentOwner], $ownerFrame] == $PeerGroupPlaceholder ∨
#if ExperimentalObjectModel
   ¬(h[h[h[o, $FirstConsistentOwner],$ownerRef],$validfor][h[h[o, $FirstConsistentOwner], $ownerFrame]]) ));
#else
   ¬(h[h[h[o, $FirstConsistentOwner], $ownerRef], $inv] <: h[h[o, $FirstConsistentOwner], $ownerFrame]) ∨
   h[h[h[o, $FirstConsistentOwner], $ownerRef], $localinv] == $BaseClass(h[h[o, $FirstConsistentOwner], $ownerFrame])));
#endif
#endif

//---------- Boxed and unboxed values

// Unboxing is functional, but boxing is not
function Box(any, ref) returns (ref);  // first arg is any because of reals and other non-int values
function Unbox(ref) returns (any);

// ...nevertheless, we still need a function that returns a new box.  It would be unsound to always
// return the same value, since each box operation at run time can return a newly allocated value.
// For soundness, we therefore need to add extra parameters to the BoxFunc function and be sure to
// pass in different values with each invocation of BoxFunc.  The way we do that is described near
// the translation of the Box expression.
type NondetType;
function MeldNondets(NondetType, any) returns (NondetType);
function BoxFunc(value: any, typ: name, occurrence: NondetType, activity: ActivityType) returns (boxedValue: ref);

axiom (∀ value: any, typ: name, occurrence: NondetType, activity: ActivityType •
  { BoxFunc(value, typ, occurrence, activity) }
  Box(value, BoxFunc(value, typ, occurrence, activity)) == BoxFunc(value, typ, occurrence, activity) ∧
  UnboxedType(BoxFunc(value, typ, occurrence, activity)) == typ);

// Sometimes boxing is just the identity function: namely when its argument is a reference type 
axiom (∀ x:ref, typ : name, occurrence: NondetType, activity : ActivityType • 
                  ¬$IsValueType(UnboxedType(x))
              ⇒ BoxFunc(x,typ, occurrence,activity) == x);

// For simplicity, we track boxed values stored to locals, not those stored into the heap.
axiom (∀ x:any, p:ref •  {Unbox(Box(x,p))}  Unbox(Box(x,p)) == x);

function UnboxedType(ref) returns (name);

// Boxes are always consistent
#if ExperimentalObjectModel
axiom (∀ p: ref •  {$IsValueType(UnboxedType(p))}  $IsValueType(UnboxedType(p))  ⇒
  (∀ heap: [ref,<x>name]x, x: any •  {heap[Box(x,p),$inv]} {heap[Box(x,p),$validfor]}  IsHeap(heap)  ⇒
    heap[Box(x,p),$inv] == $typeof(Box(x,p)) ∧ (∀ T: name • {heap[Box(x,p),$validfor][T]} heap[Box(x,p),$validfor][T])));
#elsif !TrivialObjectModel
axiom (∀ p: ref •  {$IsValueType(UnboxedType(p))}  $IsValueType(UnboxedType(p))  ⇒
  (∀ heap: [ref,<x>name]x, x: any •  {heap[Box(x,p),$inv]}  IsHeap(heap)  ⇒
    heap[Box(x,p),$inv] == $typeof(Box(x,p)) ∧ heap[Box(x,p),$localinv] == $typeof(Box(x,p))));
#endif

// For reference types, boxing returns the reference
axiom (∀ x:any, p:ref •  {UnboxedType(Box(x,p)) <: System.Object}  UnboxedType(Box(x,p)) <: System.Object ∧ Box(x,p) == p  ⇒  x == p);

// BoxTester is the value type equivalent of $As
function BoxTester(p:ref, typ: name) returns (ref);
axiom (∀ p:ref, typ: name •  {BoxTester(p,typ)}  UnboxedType(p) == typ  ⇔  BoxTester(p,typ) ≠ null);
axiom (∀ p:ref, typ: name •  {BoxTester(p,typ)}  BoxTester(p,typ) ≠ null  ⇒  Box(Unbox(p),p) == p);

//---------- Various sized integers

const unique System.SByte : name;  // sbyte
axiom $IsValueType(System.SByte);
const unique System.Byte : name;  // byte
axiom $IsValueType(System.Byte);
const unique System.Int16 : name;  //short
axiom $IsValueType(System.Int16);
const unique System.UInt16 : name;  // ushort
axiom $IsValueType(System.UInt16);
const unique System.Int32 : name;  // int
axiom $IsValueType(System.Int32);
const unique System.UInt32 : name;  // uint
axiom $IsValueType(System.UInt32);
const unique System.Int64 : name;  // long
axiom $IsValueType(System.Int64);
const unique System.UInt64 : name;  // ulong
axiom $IsValueType(System.UInt64);
const unique System.Char : name;  // char
axiom $IsValueType(System.Char);
const unique System.UIntPtr : name;
axiom $IsValueType(System.UIntPtr);
const unique System.IntPtr : name;
axiom $IsValueType(System.IntPtr);

const int#m2147483648: int;  // System.Int32.MinValue
const int#2147483647: int;  // System.Int32.MaxValue
const int#4294967295: int;  // System.UInt32.MaxValue
const int#m9223372036854775808: int;  // System.Int64.MinValue
const int#9223372036854775807: int;  // System.Int64.MaxValue
const int#18446744073709551615: int;  // System.UInt64.MaxValue

axiom int#m9223372036854775808 < int#m2147483648;
axiom int#m2147483648 < -100000;
axiom 100000 < int#2147483647;
axiom int#2147483647 < int#4294967295;
axiom int#4294967295 < int#9223372036854775807;
axiom int#9223372036854775807 < int#18446744073709551615;

axiom int#m9223372036854775808 + 1 == - int#9223372036854775807;
axiom int#m2147483648 + 1 == - int#2147483647;

function InRange(i: int, T: name) returns (bool);
axiom (∀ i:int • InRange(i, System.SByte)  ⇔  -128 ≤ i ∧ i < 128);
axiom (∀ i:int • InRange(i, System.Byte)  ⇔  0 ≤ i ∧ i < 256);
axiom (∀ i:int • InRange(i, System.Int16)  ⇔  -32768 ≤ i ∧ i < 32768);
axiom (∀ i:int • InRange(i, System.UInt16)  ⇔  0 ≤ i ∧ i < 65536);
axiom (∀ i:int • InRange(i, System.Int32)  ⇔  int#m2147483648 ≤ i ∧ i ≤ int#2147483647);
axiom (∀ i:int • InRange(i, System.UInt32)  ⇔  0 ≤ i ∧ i ≤ int#4294967295);
axiom (∀ i:int • InRange(i, System.Int64)  ⇔  int#m9223372036854775808 ≤ i ∧ i ≤ int#9223372036854775807);
axiom (∀ i:int • InRange(i, System.UInt64)  ⇔  0 ≤ i ∧ i ≤ int#18446744073709551615);
axiom (∀ i:int • InRange(i, System.Char)  ⇔  0 ≤ i ∧ i < 65536);


//---------- Type conversions and sizes


function $IntToInt(val: int, fromType: name, toType: name) returns (int);
function $IntToReal(int, fromType: name, toType: name) returns (real);
function $RealToInt(real, fromType: name, toType: name) returns (int);
function $RealToReal(val: real, fromType: name, toType: name) returns (real);

axiom (∀ z: int, B: name, C: name • InRange(z, C) ⇒ $IntToInt(z, B, C) == z);

function $SizeIs (name, int) returns (bool); // SizeIs(T,n) means that n = sizeof(T)



//------------ Formula/term operators

function $IfThenElse (bool, any, any) returns (any);

axiom (∀ b:bool, x:any, y:any • {$IfThenElse(b,x,y)} b ⇒  $IfThenElse(b,x,y) == x);
axiom (∀ b:bool, x:any, y:any • {$IfThenElse(b,x,y)} ¬b ⇒  $IfThenElse(b,x,y) == y);

//------------ Bit-level operators

function #neg (int) returns (int);
function #and (int, int) returns (int);
function #or (int, int) returns (int);
function #xor (int, int) returns (int);
function #shl (int, int) returns (int);
function #shr (int, int) returns (int);

function #rneg(real) returns (real);
function #radd(real, real) returns (real);
function #rsub(real, real) returns (real);
function #rmul(real, real) returns (real);
function #rdiv(real, real) returns (real);
function #rmod(real, real) returns (real);
function #rLess(real, real) returns (bool);
function #rAtmost(real, real) returns (bool);
function #rEq(real, real) returns (bool);
function #rNeq(real, real) returns (bool);
function #rAtleast(real, real) returns (bool);
function #rGreater(real, real) returns (bool);


//----------- Properties of operators

// the connection between % and /
axiom (∀ x:int, y:int • {x % y} {x / y}  x % y == x - x / y * y);

// remainder is C# is complicated, because division rounds toward 0
axiom (∀ x:int, y:int • {x % y}  0 ≤ x ∧ 0 < y  ⇒  0 ≤ x % y  ∧  x % y < y);
axiom (∀ x:int, y:int • {x % y}  0 ≤ x ∧ y < 0  ⇒  0 ≤ x % y  ∧  x % y < -y);
axiom (∀ x:int, y:int • {x % y}  x ≤ 0 ∧ 0 < y  ⇒  -y < x % y  ∧  x % y ≤ 0);
axiom (∀ x:int, y:int • {x % y}  x ≤ 0 ∧ y < 0  ⇒  y < x % y  ∧  x % y ≤ 0);

axiom (∀ x:int, y:int • {(x + y) % y}  0 ≤ x ∧ 0 ≤ y  ⇒  (x + y) % y == x % y);
// do we need this symmetric one, too?
axiom (∀ x:int, y:int • {(y + x) % y}  0 ≤ x ∧ 0 ≤ y  ⇒  (y + x) % y == x % y);
axiom (∀ x:int, y:int • {(x - y) % y}  0 ≤ x-y ∧ 0 ≤ y  ⇒  (x - y) % y == x % y);

// the following axiom prevents a matching loop in Simplify
// axiom (∀ x:int, y:int • {x * y / y * y}  x * y / y * y == x * y);

// the following axiom has some unfortunate matching, but it does state a property about % that
// is sometime useful
axiom (∀ a: int, b: int, d: int • { a % d, b % d } 2 ≤ d ∧ a % d == b % d ∧ a < b  ⇒  a + d ≤ b);

#if ArithDistributionAxioms
//  These axioms provide good functionality, but in some cases they can be very expensive
// distributions of * and +/-
axiom (∀ x: int, y: int, z: int •  { (x+y)*z }  (x+y)*z == x*z + y*z);
axiom (∀ x: int, y: int, z: int •  { (x-y)*z }  (x-y)*z == x*z - y*z);
axiom (∀ x: int, y: int, z: int •  { z*(x+y) }  z*(x+y) == z*x + z*y);
axiom (∀ x: int, y: int, z: int •  { z*(x-y) }  z*(x-y) == z*x - z*y);
#endif

axiom (∀ x: int, y: int • { #and(x,y) }  0 ≤ x ∨ 0 ≤ y  ⇒  0 ≤ #and(x,y));
axiom (∀ x: int, y: int • { #or(x,y) }  0 ≤ x ∧ 0 ≤ y  ⇒  0 ≤ #or(x,y) ∧ #or(x,y) ≤ x + y);

axiom (∀ i:int • {#shl(i,0)} #shl(i,0) == i);
axiom (∀ i:int, j:int • {#shl(i,j)}  1 ≤ j ⇒ #shl(i,j) == #shl(i,j-1) * 2);
axiom (∀ i:int, j:int • {#shl(i,j)} 0 ≤ i ∧ i < 32768 ∧ 0 ≤ j ∧ j ≤ 16  ⇒  0 ≤ #shl(i, j) ∧ #shl(i, j) ≤ int#2147483647);

axiom (∀ i:int • {#shr(i,0)} #shr(i,0) == i);
axiom (∀ i:int, j:int • {#shr(i,j)} 1 ≤ j ⇒ #shr(i,j) == #shr(i,j-1) / 2);


function #min(int, int) returns (int);
function #max(int, int) returns (int);
axiom (∀ x: int, y: int • { #min(x,y) } (#min(x,y) == x ∨ #min(x,y) == y) ∧ #min(x,y) ≤ x ∧ #min(x,y) ≤ y);
axiom (∀ x: int, y: int • { #max(x,y) } (#max(x,y) == x ∨ #max(x,y) == y) ∧ x ≤ #max(x,y) ∧ y ≤ #max(x,y));


//---------- Properties of String (Literals)

function #System.String.IsInterned$System.String$notnull([ref,<x>name]x, ref) returns (ref);
function #System.String.Equals$System.String([ref,<x>name]x, ref, ref) returns (bool);
function #System.String.Equals$System.String$System.String([ref,<x>name]x, ref, ref) returns (bool);
function ##StringEquals(ref, ref) returns (bool);

// two names for String.Equals
axiom (∀ h: [ref,<x>name]x, a: ref, b: ref •
 { #System.String.Equals$System.String(h, a, b) }
 #System.String.Equals$System.String(h, a, b) == #System.String.Equals$System.String$System.String(h, a, b));

// String.Equals is independent of the heap, and it is reflexive and commutative
axiom (∀ h: [ref,<x>name]x, a: ref, b: ref •
 { #System.String.Equals$System.String$System.String(h, a, b) }
 #System.String.Equals$System.String$System.String(h, a, b) == ##StringEquals(a, b) ∧
 #System.String.Equals$System.String$System.String(h, a, b) == ##StringEquals(b, a) ∧
 (a == b  ⇒  ##StringEquals(a, b)));

// String.Equals is also transitive
axiom (∀ a: ref, b: ref, c: ref •  ##StringEquals(a, b) ∧ ##StringEquals(b, c)  ⇒  ##StringEquals(a, c));

// equal strings have the same interned ref
axiom (∀ h: [ref,<x>name]x, a: ref, b: ref •
 { #System.String.Equals$System.String$System.String(h, a, b) }
 a ≠ null ∧ b ≠ null ∧ #System.String.Equals$System.String$System.String(h, a, b)
 ⇒
 #System.String.IsInterned$System.String$notnull(h, a) == 
 #System.String.IsInterned$System.String$notnull(h, b));

//-----------MAF HACK for unknown value
const $UnknownRef : ref;

// ************** END PRELUDE **************
