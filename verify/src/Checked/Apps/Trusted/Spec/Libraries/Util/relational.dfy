////////////////////////////////////////////
//  Relational interface used by SymDiff
////////////////////////////////////////////

function left<t>(x:t) : t { x }
function right<t>(x:t) : t { x }

function app_approves_disclosure(lpacket:seq<int>, rpacket:seq<int>, num_words_per_packet:int) : bool

