include "..\Libraries\Math\power2.dfy"
include "..\Assembly.dfy"
include "..\Libraries\Util\arrays_and_seqs.dfy"
include "..\Libraries\Util\relational.dfy"

///////////////////////////////////////
//        App Spec Interface
///////////////////////////////////////

// App must specify an invariant on values it wants to write to the TPM then read later with assurance of integrity
function TPM_app_policy_okay_to_trust(trusted_data:seq<int>) : bool

///////////////////////////////////////
//      Verve Entry Interface
///////////////////////////////////////

// Invariant that must be true on Verve entry, and that remains true throughout TPM executions
function TPM_satisfies_integrity_policy(aTPM:TPM_struct) : bool
{
	TPM_valid(aTPM) &&
	(forall a :: 0 <= a < |aTPM.NVRAM| && aTPM.NV_perms_ok[a] && aTPM.NV_locked ==> |aTPM.NVRAM[a]| == NV_size() && (TPM_app_policy_okay_to_trust(aTPM.NVRAM[a]) || aTPM.NVRAM[a] == newly_created_NV_value()))
}

// Bootloader must provide the hash of the TPM_PCR_COMPOSITE structure describing PCR 17 & 18
var Verve_PCR_val:seq<int>;  

// Verve entry should include:
// requires byte_seq(Verve_PCR_val, 20);
// requires TPM_valid(TPM);
// requires TPM_satisfies_integrity_policy(TPM);
// requires TPM.PCR_19 == [[-1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1]];

////////////////////////////////////////////////////////////
//            Basic functions and datatypes
// (Note: Sec. 2.1.1 of Part 2: Everything is big endian)
////////////////////////////////////////////////////////////

datatype CommandState = Idle | Ready | CmdReception | Executing | CmdComplete;

datatype TPM_struct = TPM_build(	
	PCR_19  : seq<seq<int>>,
	NVRAM : seq<seq<int>>,
	NV_locked : bool,				// Is the TPM enforcing NV restrictions?	
	NV_perms_ok : seq<bool>,
	cmd_state : CommandState,
	cmd_buf   : seq<int>,
	reply_buf : seq<int>,
	random_index : int			// Tracks our current position in the stream of randomness from the TPM
	);

function TPM_valid(aTPM:TPM_struct) : bool	
{
	|aTPM.NVRAM| == |aTPM.NV_perms_ok| && 
	word(|aTPM.NVRAM|) &&	
	(forall i {:trigger byte_seq(aTPM.PCR_19[i], 20)} :: 0 <= i < |aTPM.PCR_19| ==> byte_seq(aTPM.PCR_19[i], 20)) &&	// Must be sets of 20 bytes
	(forall i {:trigger byte(aTPM.cmd_buf[i])} :: 0 <= i < |aTPM.cmd_buf|   ==> byte(aTPM.cmd_buf[i])) &&
	(forall i {:trigger byte(aTPM.reply_buf[i])} :: 0 <= i < |aTPM.reply_buf| ==> byte(aTPM.reply_buf[i])) &&
	(forall a :: valid_nv_index(aTPM, a) ==> word(|aTPM.NVRAM[a]|+14) && is_byte_seq(aTPM.NVRAM[a]))	// Added +14 because size of read rely must be a word
}

// We model the infinite stream of randomness as a series of "constants" returned
// by this function that are discovered by calls to read_random
function read_random_byte(index:int) : int

// We only use this for 17 & 18, which don't change while we're executing
function PCR_val(index:int) : seq<int>

// Tracks whether we have taken control of the TPM at access level 3
// Tracked via a function, since it cannot change while we execute
function Locality3_requested() :  bool
function Locality3_obtained() :  bool


ghost var TPM:TPM_struct;

// "Constants"
function NV_size() : int
	ensures NV_size() < power2(32);
	ensures NV_size() < power2(32) - 22;
 { reveal_power2(); 256 }

function valid_nv_index(aTPM:TPM_struct, a:int) : bool
{
	0 <= a < |aTPM.NVRAM| && 0 <= a < |aTPM.NV_perms_ok| 
}

function newly_created_NV_value() : seq<int>
	ensures byte_seq(newly_created_NV_value(), NV_size());
{
	seq_of_ff(NV_size())
}

function seq_of_ff(count:int) : seq<int>
	requires word(count);
	ensures |seq_of_ff(count)| == count;
	ensures is_byte_seq(seq_of_ff(count));
{
	if count <= 0 then
		[ ]
	else 
		[ 0xff ] + seq_of_ff(count - 1)
}

// Condenses all of the public information in the TPM
// I.e., public = PCR_19 + all NVRAM for which !perms_ok
function TPM_public(aTPM:TPM_struct) : set<seq<int>>
	requires TPM_valid(aTPM);
{
	(set i:int | 0 <= i < |aTPM.PCR_19| :: aTPM.PCR_19[i]) +
	(set a:int | 0 <= a < |aTPM.NVRAM| && 0 <= a < |aTPM.NV_perms_ok| && (!aTPM.NV_perms_ok[a] || !aTPM.NV_locked) :: aTPM.NVRAM[a])
}

/********************************************************
 *  Low-level TPM interactions
 ********************************************************/

// Template for TPM operations
//  modifies this;  // Except...
//	ensures old(TPM.PCR_19)			== TPM.PCR_19;
//	ensures old(TPM.NVRAM)			== TPM.NVRAM;
//  ensures old(TPM.NV_locked)		== TPM.NV_locked;
//	ensures old(TPM.NV_perms_ok)	== TPM.NV_perms_ok;
//	ensures old(TPM.cmd_state)		== TPM.cmd_state;
//	ensures old(TPM.cmd_buf)		== TPM.cmd_buf;
//	ensures old(TPM.reply_buf)		== TPM.reply_buf;
//  ensures old(Verve_PCR_val)      == Verve_PCR_val;
//	ensures old(TPM.random_index)	== TPM.random_index;

// movb 2 -> 0xFED43000  (0xFED4 || TPM_ACCESS_3 (3000h))
method {:axiom} request_access()
  ensures Locality3_requested();

// movb 0xFED43000 -> eax
method {:axiom} check_access_status() returns (status:int)
  requires Locality3_requested();
  requires word(32);  // Needed to satisfy BitwiseAndInstruction's precondition
  ensures byte(status) && word(status);	// Needed to satisfy BitwiseAndInstruction's precondition
  ensures BitwiseAndInstruction(status, 32) > 0 ==> Locality3_obtained();   // bit 5 = activeLocality

method {:axiom} issue_command_ready()
	// movb 0x40 -> 0xFED43018	
  requires Locality3_obtained();
	requires TPM_valid(TPM);
	requires byte_seq(Verve_PCR_val, 20);
	requires TPM.cmd_state.Idle? || TPM.cmd_state.Ready? || TPM.cmd_state.CmdReception? || TPM.cmd_state.Executing? || TPM.cmd_state.CmdComplete?;
	ensures old(TPM.cmd_state.Idle?) || old(TPM.cmd_state.Ready?) ==> TPM.cmd_state == Ready;		
	ensures old(TPM.cmd_state.CmdReception? || TPM.cmd_state.Executing? || TPM.cmd_state.CmdComplete?) ==> TPM.cmd_state == Idle;
	ensures TPM.cmd_buf == [] && TPM.reply_buf == [];
	modifies this; // Except...
	ensures old(TPM.PCR_19)			== TPM.PCR_19;
	ensures old(TPM.NVRAM)			== TPM.NVRAM;	
	ensures old(TPM.NV_locked)		== TPM.NV_locked;
	ensures old(TPM.NV_perms_ok)	== TPM.NV_perms_ok;
	//ensures old(TPM.cmd_state)		== TPM.cmd_state;
	//ensures old(TPM.cmd_buf)		== TPM.cmd_buf;
	//ensures old(TPM.reply_buf)		== TPM.reply_buf;
	ensures old(Verve_PCR_val)      == Verve_PCR_val;
	ensures old(TPM.random_index)	== TPM.random_index;

method {:axiom} write_FIFO(c:int)
	// movb c -> 0xFED43024	
  requires Locality3_obtained();
	requires TPM_valid(TPM);
	requires byte_seq(Verve_PCR_val, 20);
	requires byte(c);
	requires TPM.cmd_state.Ready? || TPM.cmd_state.CmdReception?;
	ensures  TPM.cmd_state == CmdReception;
	ensures  TPM.cmd_buf == old(TPM.cmd_buf) + [c];
	modifies this; // Except...
	ensures old(TPM.PCR_19)			== TPM.PCR_19;
	ensures old(TPM.NVRAM)			== TPM.NVRAM;
	ensures old(TPM.NV_locked)		== TPM.NV_locked;
	ensures old(TPM.NV_perms_ok)	== TPM.NV_perms_ok;
	//ensures old(TPM.cmd_state)		== TPM.cmd_state;
	//ensures old(TPM.cmd_buf)		== TPM.cmd_buf;
	ensures old(TPM.reply_buf)		== TPM.reply_buf;
	ensures old(Verve_PCR_val)      == Verve_PCR_val;
	ensures old(TPM.random_index)	== TPM.random_index;

method {:axiom} go()
	// movb 0x20 -> 0xFED43018
  requires Locality3_obtained();
	requires TPM_valid(TPM);
	requires byte_seq(Verve_PCR_val, 20);
	requires forall new_TPM : TPM_struct :: async_TPM_execution(TPM, new_TPM, Verve_PCR_val) ==> TPM_satisfies_integrity_policy(new_TPM);
	requires TPM.cmd_state.CmdReception?;
	ensures  TPM.cmd_state == Executing;
	modifies this; // Except...
	ensures old(TPM.PCR_19)			== TPM.PCR_19;
	ensures old(TPM.NVRAM)			== TPM.NVRAM;
	ensures old(TPM.NV_locked)		== TPM.NV_locked;
	ensures old(TPM.NV_perms_ok)	== TPM.NV_perms_ok;
	//ensures old(TPM.cmd_state)		== TPM.cmd_state;
	ensures old(TPM.cmd_buf)		== TPM.cmd_buf;
	ensures old(TPM.reply_buf)		== TPM.reply_buf;
	ensures old(Verve_PCR_val)      == Verve_PCR_val;
	ensures old(TPM.random_index)	== TPM.random_index;

// Provide relational requirements on go()
method {:axiom} go\relates_to\go()
	requires TPM_valid(TPM);	
	requires byte_seq(Verve_PCR_val, 20);
	requires forall new_TPM : TPM_struct :: TPM_valid(new_TPM) && async_TPM_execution(TPM, new_TPM, Verve_PCR_val) ==> TPM_public(left(new_TPM)) == TPM_public(right(new_TPM));

method {:axiom} check_data_available() returns (r:int)
	// movb 0xFED43018 -> (byte) r
  requires Locality3_obtained();
	requires TPM_valid(TPM);
	requires byte_seq(Verve_PCR_val, 20);
	requires TPM.cmd_state.Executing? || TPM.cmd_state.CmdComplete?;
	ensures  old(TPM.cmd_state.Executing?)		==> byte_seq(Verve_PCR_val, 20) &&	// Doesn't change hash's validity
													async_TPM_execution(old(TPM), TPM, Verve_PCR_val) &&  // May bump us to CmdComplete, or may leave us in Executing
												    (r == 0x90 <==> TPM.cmd_state.CmdComplete?);		// 0x90 = TIS_STS_VALID (0x80) + TIS_STS_DATA_AVAIL (0x10)
	ensures old(TPM.cmd_state.CmdComplete?) ==> (r == 0x90 <==> |TPM.reply_buf| > 0) && old(TPM) == TPM;
	modifies this;  // Except... (specified by Async_TPM, so no additional details below)
	//ensures old(TPM.PCR_19)			== TPM.PCR_19;
	//ensures old(TPM.NVRAM)			== TPM.NVRAM;
	//ensures old(TPM.NV_locked)		== TPM.NV_locked;	
	//ensures old(TPM.NV_perms_ok)	== TPM.NV_perms_ok;
	//ensures old(TPM.cmd_state)		== TPM.cmd_state;
	//ensures old(TPM.cmd_buf)		== TPM.cmd_buf;
	//ensures old(TPM.reply_buf)		== TPM.reply_buf;
	ensures old(Verve_PCR_val)      == Verve_PCR_val;

method {:axiom} read_FIFO() returns (c:int)
	// movb 0xFED43024 -> c
  requires Locality3_obtained();
	requires TPM_valid(TPM);
	requires byte_seq(Verve_PCR_val, 20);
	requires TPM.cmd_state.CmdComplete? && |TPM.reply_buf| > 0;
	ensures old(TPM.reply_buf) == [c] + TPM.reply_buf;
	ensures byte(c);
	modifies this;  // Except...
	ensures old(TPM.PCR_19)			== TPM.PCR_19;
	ensures old(TPM.NVRAM)			== TPM.NVRAM;
	ensures old(TPM.NV_locked)		== TPM.NV_locked;
	ensures old(TPM.NV_perms_ok)	== TPM.NV_perms_ok;
	ensures old(TPM.cmd_state)		== TPM.cmd_state;
	ensures old(TPM.cmd_buf)		== TPM.cmd_buf;
	//ensures old(TPM.reply_buf)		== TPM.reply_buf;
	ensures old(Verve_PCR_val)      == Verve_PCR_val;
	ensures old(TPM.random_index)	== TPM.random_index;


function async_TPM_execution(old_TPM:TPM_struct, new_TPM:TPM_struct, the_Verve_PCR_val:seq<int>) : bool
	requires TPM_valid(old_TPM);
	requires byte_seq(the_Verve_PCR_val, 20);
{
	// We execute a valid command
	(  TPM_read(old_TPM, new_TPM) ||
	   TPM_write(old_TPM, new_TPM) ||
	   TPM_extend(old_TPM, new_TPM) ||
	   TPM_check_perms(old_TPM, new_TPM, the_Verve_PCR_val) ||
	   TPM_check_locked(old_TPM, new_TPM) ||
	   TPM_quote(old_TPM, new_TPM) ||
     TPM_get_random(old_TPM, new_TPM) ||
     TPM_PCR_read(old_TPM, new_TPM) 
	  // || TPM_...
	 ) 
	||
	// Or there's a valid command present, but the TPM is still executing it
	(valid_cmd_present(old_TPM) && old_TPM == new_TPM) 
	|| 
	// Or there's an unexpected command, so we know nothing about the TPM's state
	!valid_cmd_present(old_TPM)
	// havoc!
	
}


function valid_read_cmd(s:seq<int>) : bool 
{
	exists a:int :: word(a) && s == encode_read_cmd(a)
}

function valid_write_cmd(s:seq<int>) : bool 
{
	exists a:int, v:seq<int> ::  word(a) &&	|v| == NV_size() &&  s == encode_write_cmd(a, v)
}

function valid_PCR_extend_cmd(s:seq<int>) : bool 
{
	exists data:seq<int> :: byte_seq(data, 20) && s == encode_PCR_extend_cmd(data)
}

function valid_check_perms_cmd(s:seq<int>) : bool 
{
	exists a:int :: word(a) && s == encode_check_perms_cmd(a)
}

function valid_check_locked_cmd(s:seq<int>) : bool 
{
	s == encode_check_locked_cmd()
}

function valid_quote_cmd(s:seq<int>) : bool 
{
	exists hmac:seq<int>, nonce_external:seq<int>, key_handle:seq<int>, auth_handle:seq<int>, nonce_odd:seq<int>, nonce_even:seq<int> :: 
			byte_seq(hmac, 20) && byte_seq(nonce_external, 20) && byte_seq(key_handle, 4) && byte_seq(auth_handle, 4) && byte_seq(nonce_odd, 20) && byte_seq(nonce_even, 20) &&
			(s == encode_quote_cmd(hmac, nonce_external, key_handle, auth_handle, nonce_odd, nonce_even))
}

function valid_get_random_cmd(s:seq<int>) : bool
{
  exists a:int :: 0 <= a < 256 && s == encode_get_random_cmd(a)
}

function valid_PCR_read_cmd(s:seq<int>) : bool
{
  exists a:int :: (a == 17 || a == 18) &&	s == encode_pcr_read_cmd(a)
}

function valid_cmd(s:seq<int>) : bool 
{
	valid_read_cmd          (s) ||
	valid_write_cmd			(s) ||
	valid_PCR_extend_cmd	(s) ||
	valid_check_perms_cmd	(s) ||
	valid_check_locked_cmd	(s) ||
	valid_quote_cmd			(s) ||
  valid_get_random_cmd (s) ||
  valid_PCR_read_cmd (s)
}

function valid_cmd_present(aTPM:TPM_struct) : bool 
	requires TPM_valid(aTPM);
{
	valid_cmd(aTPM.cmd_buf)
}


function command_executed(old_TPM:TPM_struct, new_TPM:TPM_struct) : bool
{
	old_TPM.PCR_19			== new_TPM.PCR_19 &&
	old_TPM.NVRAM			== new_TPM.NVRAM &&
	old_TPM.NV_locked		== new_TPM.NV_locked &&
	old_TPM.NV_perms_ok		== new_TPM.NV_perms_ok &&
	new_TPM.cmd_state.CmdComplete? &&
	old_TPM.cmd_buf			== new_TPM.cmd_buf &&
	old_TPM.random_index	== new_TPM.random_index
}


/********************************************************
 *  Semantic-level TPM Commands
 ********************************************************/

function TPM_read(old_TPM:TPM_struct, new_TPM:TPM_struct) : bool
	requires TPM_valid(old_TPM);
{
	(exists a:int :: word(a) &&
		old_TPM.cmd_buf == encode_read_cmd(a) &&
		(!is_error_reply(new_TPM.reply_buf) ==> 
			valid_nv_index(old_TPM, a) && new_TPM.reply_buf == encode_read_reply(old_TPM.NVRAM[a]))		
	)
	&& command_executed(old_TPM, new_TPM)
}


function TPM_write(old_TPM:TPM_struct, new_TPM:TPM_struct) : bool
	requires TPM_valid(old_TPM);
{
	(exists a:int, v:seq<int> :: word(a) && 0 < |v| == NV_size() &&
		old_TPM.cmd_buf == encode_write_cmd(a, v) &&
		// If we get a successful reply, then the NVRAM has been updated to v
		(!is_error_reply(new_TPM.reply_buf) ==> valid_nv_index(new_TPM, a) && new_TPM.NVRAM[a] == v) &&
		// If the NVRAM at that location was updated, it was updated to v
		(valid_nv_index(old_TPM, a) && valid_nv_index(new_TPM, a) && new_TPM.NVRAM[a] != old_TPM.NVRAM[a] ==> new_TPM.NVRAM[a] == v) &&
		// All other NVRAM locations are unaffected
		(forall a':int ::
			valid_nv_index(old_TPM, a') && valid_nv_index(new_TPM, a') && a' != a ==>
			new_TPM.NVRAM[a'] == old_TPM.NVRAM[a'])) &&
	|new_TPM.reply_buf| > 0 &&	
	is_byte_seq(new_TPM.reply_buf) &&
	old_TPM.PCR_19			== new_TPM.PCR_19 &&
	|old_TPM.NVRAM|			== |new_TPM.NVRAM| &&
	old_TPM.NV_locked		== new_TPM.NV_locked &&
	old_TPM.NV_perms_ok		== new_TPM.NV_perms_ok &&
	new_TPM.cmd_state.CmdComplete? &&
	old_TPM.cmd_buf			== new_TPM.cmd_buf &&
	old_TPM.random_index	== new_TPM.random_index
}

function TPM_extend(old_TPM:TPM_struct, new_TPM:TPM_struct) : bool
	requires TPM_valid(old_TPM);
	//reads this;
{
	(exists data:seq<int> :: byte_seq(data, 20) &&
		old_TPM.cmd_buf == encode_PCR_extend_cmd(data) &&
		// The PCR was successfully updated
		(!is_error_reply(new_TPM.reply_buf) ==> new_TPM.PCR_19 == old_TPM.PCR_19 + [data]) &&
		// If it was updated at all, it was updated with data
		(new_TPM.PCR_19 == old_TPM.PCR_19 || new_TPM.PCR_19 == old_TPM.PCR_19 + [data]))
	&& 
	is_byte_seq(new_TPM.reply_buf) && |new_TPM.reply_buf| > 0 &&
	old_TPM.NVRAM			== new_TPM.NVRAM &&
	old_TPM.NV_locked		== new_TPM.NV_locked &&
	old_TPM.NV_perms_ok		== new_TPM.NV_perms_ok &&
	new_TPM.cmd_state.CmdComplete? &&
	old_TPM.cmd_buf			== new_TPM.cmd_buf && 
	old_TPM.random_index	== new_TPM.random_index
}

function TPM_check_perms(old_TPM:TPM_struct, new_TPM:TPM_struct, the_Verve_PCR_val:seq<int>) : bool
	requires TPM_valid(old_TPM);
	requires byte_seq(the_Verve_PCR_val, 20);
{
	(exists a:int :: word(a) &&
		old_TPM.cmd_buf   == encode_check_perms_cmd(a) &&
		(new_TPM.reply_buf == encode_check_perms_reply(a, the_Verve_PCR_val, NV_size()) ==>
			valid_nv_index(old_TPM, a) && old_TPM.NV_perms_ok[a] ))
	&& is_byte_seq(new_TPM.reply_buf) && |new_TPM.reply_buf| > 0
	&& command_executed(old_TPM, new_TPM)
}

function TPM_check_locked(old_TPM:TPM_struct, new_TPM:TPM_struct) : bool
	requires TPM_valid(old_TPM);
{
	old_TPM.cmd_buf == encode_check_locked_cmd() &&
	(new_TPM.reply_buf == encode_check_locked_reply(old_TPM) || is_error_reply(new_TPM.reply_buf)) &&	
	is_byte_seq(new_TPM.reply_buf) &&
	command_executed(old_TPM, new_TPM)
}

function TPM_quote(old_TPM:TPM_struct, new_TPM:TPM_struct) : bool
{
	exists hmac:seq<int>, nonce_external:seq<int>, key_handle:seq<int>, auth_handle:seq<int>, nonce_odd:seq<int>, nonce_even:seq<int> ::
		   (byte_seq(hmac, 20) && byte_seq(nonce_external, 20) && byte_seq(key_handle, 4) && byte_seq(auth_handle, 4) && byte_seq(nonce_odd, 20) && byte_seq(nonce_even, 20)) &&		   
		(old_TPM.cmd_buf == encode_quote_cmd(hmac, nonce_external, key_handle, auth_handle, nonce_odd, nonce_even) &&
		(is_error_reply(new_TPM.reply_buf) || Verve_quote(new_TPM.reply_buf, nonce_external, old_TPM.PCR_19)) && 
		 0 < |new_TPM.reply_buf| <= power2(33) && is_byte_seq(new_TPM.reply_buf))
	&& command_executed(old_TPM, new_TPM)
}

function TPM_get_random(old_TPM:TPM_struct, new_TPM:TPM_struct) : bool
	requires TPM_valid(old_TPM);
{
	(exists a:int, rand_bytes:seq<int> :: 0 <= a < 256 &&
		is_byte_seq(rand_bytes) && |rand_bytes| <= a && word(|rand_bytes|+14) &&
		old_TPM.cmd_buf == encode_get_random_cmd(a) &&
		(!is_error_reply(new_TPM.reply_buf) ==> 
			new_TPM.reply_buf == encode_get_random_reply(rand_bytes)
			&& new_TPM.random_index == old_TPM.random_index + |rand_bytes|
			&& (forall j :: old_TPM.random_index <= j < new_TPM.random_index ==> read_random_byte(j) == rand_bytes[j - old_TPM.random_index])
		)		
	)
	&& 
	old_TPM.PCR_19			== new_TPM.PCR_19 &&
	old_TPM.NVRAM			== new_TPM.NVRAM &&
	old_TPM.NV_locked		== new_TPM.NV_locked &&
	old_TPM.NV_perms_ok		== new_TPM.NV_perms_ok &&
	new_TPM.cmd_state.CmdComplete? &&
	old_TPM.cmd_buf			== new_TPM.cmd_buf
}

function TPM_PCR_read(old_TPM:TPM_struct, new_TPM:TPM_struct) : bool
	requires TPM_valid(old_TPM);
{
	(exists a:int, pcr_val:seq<int> :: (a == 17 || a == 18) &&
		is_byte_seq(pcr_val) && |pcr_val| == 20 && word(30) &&
		old_TPM.cmd_buf == encode_pcr_read_cmd(a) &&
		(!is_error_reply(new_TPM.reply_buf) ==> 
			new_TPM.reply_buf == encode_pcr_read_reply(pcr_val) &&
      PCR_val(a) == pcr_val      
      )		
	)
	&& command_executed(old_TPM, new_TPM)
}

/***************************************
 *	TPM Tags
 ***************************************/
function TPM_TAG_RQU_COMMAND() : seq<int>
{
	[ 0, 0xC1 ] 
}

function TPM_TAG_RQU_AUTH1_COMMAND() : seq<int>
{
	[ 0, 0xC2 ] 
}

function method TPM_TAG_RSP_COMMAND() : seq<int>
{
	[ 0, 0xC4 ] 
}

function method TPM_TAG_NV_DATA_PUBLIC() : seq<int>
{
	[ 0, 0x18 ] 
}

function method TPM_TAG_NV_ATTRIBUTES() : seq<int>
{
	[ 0, 23 ]
}

function TPM_TAG_PERMANENT_FLAGS() : seq<int>
{
	[ 0, 0x1f ] 
}

/***************************************
 *	Command Ordinals
 ***************************************/
function TPM_ORD_GetCapability() : seq<int>
{
	[ 0, 0, 0, 0x65 ] 
}

function TPM_ORD_NV_ReadValue() : seq<int>
{
	[ 0, 0, 0, 0xCF ] 
}

function TPM_ORD_NV_WriteValue() : seq<int>
{
	[ 0, 0, 0, 0xCD ] 
}

function TPM_ORD_Extend() : seq<int>
{
	[ 0, 0, 0, 0x14 ] 
}

function TPM_ORD_Quote2() : seq<int>
{
	[ 0, 0, 0, 0x3E ] 
}

function TPM_ORD_GetRandom() : seq<int>
{
	[ 0, 0, 0, 0x46 ]
}

function TPM_ORD_PcrRead() : seq<int>
{
	[ 0, 0, 0, 0x15 ]
}

function TPM_CAP_NV_INDEX() : seq<int>
{
	[ 0, 0, 0, 0x11 ] 
}

function TPM_CAP_FLAG() : seq<int>
{
	[ 0, 0, 0, 4 ]
}

function TPM_CAP_FLAG_PERMANENT() : seq<int>
{
	[ 0, 0, 0x01, 0x08 ] // 0x00000108 
}

/***************************************
 *	Return codes
 ***************************************/
function method TPM_SUCCESS() : seq<int>
{
	[ 0, 0, 0, 0 ]
}

/***************************************
 *	Encoding of TPM Commands
 ***************************************/
 
function Verve_quote(data:seq<int>, nonce:seq<int>, PCR_19_history:seq<seq<int>>) : bool
	requires byte_seq(nonce, 20);

function is_error_reply(reply: seq<int>) : bool
{
    |reply| >= 10 && reply[6..10] != TPM_SUCCESS() && is_byte_seq(reply)
}

/*	 

function valid_error_code(e:int) : bool
{
	word(e) && e != 0
}

function encode_error_reply(e:int) : seq<int>
	requires valid_error_code(e);
	ensures var result := encode_error_reply(e);
			|result| >= 10 &&
			result[6..10] != TPM_SUCCESS();

*/

function encode_read_cmd(a:int) : seq<int>
	requires word(a);
	ensures var result := encode_read_cmd(a);
			|result| == result[5];	// Make sure we set the size parameter correctly
{
	TPM_TAG_RQU_COMMAND() +
	[ 0, 0, 0, 22 ] +		 // # of bytes in command, counting everything
	TPM_ORD_NV_ReadValue() +
	word_to_bytes(a) +
	[ 0, 0, 0, 0] +			// No offset
	word_to_bytes(NV_size()) // # of bytes to read
}

function encode_read_reply(data:seq<int>) : seq<int>
	requires word(|data|+14);
	ensures var result := encode_read_reply(data);			
			word_to_bytes(|result|) == result[2..6];	// Make sure we set the size parameter correctly
{
	TPM_TAG_RSP_COMMAND() + 
	word_to_bytes(|data| + 14) + // # of bytes in command, counting everything
	TPM_SUCCESS() +
	word_to_bytes(|data|) +
	data
}

function encode_get_random_cmd(amt:int) : seq<int>	
	requires 0 <= amt < 256;
	ensures var result := encode_get_random_cmd(amt);
			|result| == result[5];	// Make sure we set the size parameter correctly
{
	TPM_TAG_RQU_COMMAND() +
	[ 0, 0, 0, 14 ] +		 // # of bytes in command, counting everything
	TPM_ORD_GetRandom() +
	[ 0, 0, 0, amt ]
}

// TODO: Say something about the randomness returned
function encode_get_random_reply(data:seq<int>) : seq<int>
	requires word(|data|+14);
	ensures var result := encode_get_random_reply(data);			
			word_to_bytes(|result|) == result[2..6];	// Make sure we set the size parameter correctly
{
	TPM_TAG_RSP_COMMAND() + 
	word_to_bytes(|data| + 14) + // # of bytes in command, counting everything
	TPM_SUCCESS() +
	word_to_bytes(|data|) +
	data
}

function encode_pcr_read_cmd(a:int) : seq<int>
	requires a == 17 || a == 18;
	ensures var result := encode_pcr_read_cmd(a);
			|result| == result[5];	// Make sure we set the size parameter correctly
{
	TPM_TAG_RQU_COMMAND() +
	[ 0, 0, 0, 14 ] +		 // # of bytes in command, counting everything
	TPM_ORD_PcrRead() +
	[ 0, 0, 0, a ]
}

function encode_pcr_read_reply(data:seq<int>) : seq<int>
	requires |data| == 20 && word(30);
	ensures var result := encode_pcr_read_reply(data);			
			word_to_bytes(|result|) == result[2..6];	// Make sure we set the size parameter correctly
{
	TPM_TAG_RSP_COMMAND() + 
	word_to_bytes(|data| + 10) + // # of bytes in command, counting everything
	TPM_SUCCESS() +
	data
}

function encode_write_cmd(a:int, v:seq<int>) : seq<int>	
	requires word(a);
	requires 0 < |v| == NV_size();
	ensures var result := encode_write_cmd(a, v);		
			|result| < power2(32) &&
			word_to_bytes(|result|) == result[2..6];	// Make sure we set the size parameter correctly
{
	TPM_TAG_RQU_COMMAND() +
	word_to_bytes(22 + NV_size()) + // # of bytes in command, counting everything
	TPM_ORD_NV_WriteValue() +
	word_to_bytes(a) + 
	[ 0, 0, 0, 0] +					// No offset
	word_to_bytes(NV_size()) +
	v
}

function encode_check_perms_cmd(a:int) : seq<int>
	requires word(a);
	ensures var result := encode_check_perms_cmd(a);
			|result| == result[5];	// Make sure we set the size parameter correctly
{
	TPM_TAG_RQU_COMMAND() +
	[ 0, 0, 0, 22]  +				// # of bytes in command, counting everything
	TPM_ORD_GetCapability() +
	TPM_CAP_NV_INDEX() + 
	[ 0, 0, 0, 4 ]	+				// Subcap size == sizeof(NV index) == sizeof(uint) == 4 bytes
	word_to_bytes(a) 
}

function encode_check_perms_reply(a:int, v:seq<int>, len:int) : seq<int>
	requires word(a);
	requires byte_seq(v, 20);
	requires word(len);
	ensures var result := encode_check_perms_reply(a, v, len);
		|result| == result[5];	// Make sure we set the size parameter correctly
{
	TPM_TAG_RSP_COMMAND() + 
	[ 0, 0, 0,  85 ] + // # of bytes in command, counting everything
	TPM_SUCCESS() +
	word_to_bytes(|TPM_NV_DATA_PUBLIC(a, v, len)|) +
	TPM_NV_DATA_PUBLIC(a, v, len)
}


function TPM_NV_DATA_PUBLIC(a:int, v:seq<int>, len:int) : seq<int>
	requires word(len);
	requires word(a);
	requires byte_seq(v, 20);
	ensures |TPM_NV_DATA_PUBLIC(a, v, len)| == 71;
	ensures word(|TPM_NV_DATA_PUBLIC(a, v, len)|);
{
	reveal_power2();
	TPM_TAG_NV_DATA_PUBLIC() +
	word_to_bytes(a) +
	Verve_PCR_INFO_SHORT(v) + // pcrInfoRead
	Verve_PCR_INFO_SHORT(v) + // pcrInfoWrite +
	TPM_TAG_NV_ATTRIBUTES() + [ 0, 0, 0x20, 0 ] + //TPM_NV_ATTRIBUTES + TPM_NV_PER_WRITEDEFINE=bit 13=0x20
	[ 0 ] + // bReadSTClear: Set to FALSE on each TPM_Startup(ST_Clear) and set to TRUE after a ReadValuexxx with datasize of 0
	[ 0 ] + // bWriteSTClear: Set to FALSE on each TPM_Startup(ST_CLEAR) and set to TRUE after a WriteValuexxx with a datasize of 0.	
	[ 0 ] + // bWriteDefine: Set to FALSE after TPM_NV_DefineSpace and set to TRUE after a successful WriteValuexxx with a datasize of 0
	word_to_bytes(len)
}

function method Verve_PCR_INFO_SHORT(v:seq<int>) : seq<int>
	requires byte_seq(v, 20);
	ensures |Verve_PCR_INFO_SHORT(v)| == 26;
{
	Verve_PCR_SELECTION() +
	[ 31 ] +				// localityAtRelease = 0x1f = Any locality (we're relying on PCR-based protection)
	v					
}

function method Verve_PCR_SELECTION() : seq<int>
{
	[ 0, 3, 0, 0, 6]  // pcrSelection = size (0x0003), PCR bit map.  Selects PCR 17 & 18 from byte 2 (0-indexed)	
}

function Quote_PCR_SELECTION() : seq<int>
{
	[ 0, 3, 0, 0, 14]  // pcrSelection = size (0x0003), PCR bit map.  Selects PCR 17, 18, 19 from byte 2 (0-indexed)
}


function encode_check_locked_cmd() : seq<int>
	ensures var result := encode_check_locked_cmd();
		|result| == result[5];	// Make sure we set the size parameter correctly
{
	TPM_TAG_RQU_COMMAND() +
	[ 0, 0, 0, 22]  +			// # of bytes in command, counting everything
	TPM_ORD_GetCapability() +
	TPM_CAP_FLAG() + 
	[ 0, 0, 0, 4 ]	+ // Subcap size == sizeof(uint) == 4 bytes
	TPM_CAP_FLAG_PERMANENT()
}

function encode_check_locked_reply(aTPM:TPM_struct) : seq<int>
	requires TPM_valid(aTPM);
	ensures var result := encode_check_locked_reply(aTPM);
		|result| == result[5];	// Make sure we set the size parameter correctly
{
	TPM_TAG_RSP_COMMAND() + 
	[ 0, 0, 0,  36 ] + // # of bytes in command, counting everything
	TPM_SUCCESS() +
	word_to_bytes(|TPM_PERMANENT_FLAGS(aTPM)|) +
	TPM_PERMANENT_FLAGS(aTPM)
}

function TPM_PERMANENT_FLAGS(aTPM:TPM_struct) : seq<int>
	requires TPM_valid(aTPM);
	ensures var result := TPM_PERMANENT_FLAGS(aTPM);
		|result| == 2 + 20 &&
		is_byte_seq(result) &&
		result[0..2] == TPM_TAG_PERMANENT_FLAGS() &&
		result[2+15] == if aTPM.NV_locked then 1 else 0;

function encode_PCR_extend_cmd(data:seq<int>) : seq<int>
	requires byte_seq(data, 20);
	ensures var result := encode_PCR_extend_cmd(data);
		|result| == result[5];	// Make sure we set the size parameter correctly
{
	TPM_TAG_RQU_COMMAND() +
	[ 0, 0, 0, 34]  +			// # of bytes in command, counting everything
	TPM_ORD_Extend() +
	[ 0, 0, 0, 19] +	// We only allow Verve to extend things into PCR 19
	data
}

function encode_quote_cmd(hmac:seq<int>, nonce_external:seq<int>, key_handle:seq<int>, auth_handle:seq<int>, nonce_odd:seq<int>, nonce_even:seq<int>) : seq<int>
	requires hmac_unverified(hmac, nonce_external, key_handle, auth_handle, nonce_odd, nonce_even);
	requires byte_seq(nonce_external, 20);
	requires byte_seq(key_handle, 4);
	requires byte_seq(auth_handle, 4);
	requires byte_seq(nonce_odd, 20);
	requires byte_seq(nonce_even, 20);
	ensures var result := encode_quote_cmd(hmac, nonce_external, key_handle, auth_handle, nonce_odd, nonce_even);
			|result| == result[5];	// Make sure we set the size parameter correctly
{
	TPM_TAG_RQU_AUTH1_COMMAND() +
	[ 0, 0, 0, 85]  +			// # of bytes in command, counting everything
	TPM_ORD_Quote2() +
	key_handle +
	nonce_external +
	Quote_PCR_SELECTION() +
	[ 1 ] + // When TRUE add TPM_CAP_VERSION_INFO to the output
	auth_handle +
	nonce_odd +
	[ 1 ] + // continueAuthSession?
	hmac
}

// We don't actually care about the security of the TPM's transport session,
// so this HMAC calculation needn't be verified beyond standard safety properties
function hmac_unverified(hmac:seq<int>, nonce_external:seq<int>, key_handle:seq<int>, auth_handle:seq<int>, nonce_odd:seq<int>, nonce_even:seq<int>) : bool
{ byte_seq(hmac, 20) }




