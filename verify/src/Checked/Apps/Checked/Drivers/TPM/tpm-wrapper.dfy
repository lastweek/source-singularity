include "tpm-driver.dfy"
include "..\..\Libraries\Crypto\Hash\sha1_impl.dfy"
include "..\..\Libraries\Util\arrays_and_seqs.dfy"

// Note:
// 1) In the implementation, we'll want to SHA-256 hash the public key and then do two extends (since hash output is larger than extend's input)

/***************************************************************************
 *	                    Higher-level Implementation
 ***************************************************************************/

// Store secret
// Retreive secret
// Extend PCR 19
// Quote

function method reply_is_error(reply:seq<int>) : bool
{
	 (|reply| >= 10 && reply[6..10] != [0x00, 0x00, 0x00, 0x00])
}

method extract_read_reply_data(reply:seq<int>, ghost NVRAM_contents:seq<int>) returns (data:seq<int>) 
	requires is_byte_seq(reply);
	requires is_byte_seq(NVRAM_contents);
	requires word(|NVRAM_contents|+14);
	requires reply == encode_read_reply(NVRAM_contents);
	ensures data == NVRAM_contents;
{
	data := reply[14..];
}


lemma lemma_check_perms_cmd_unique_general()
	ensures forall a, b :: word(a) && word(b) && encode_check_perms_cmd(a) == encode_check_perms_cmd(b) ==> a == b;
{
	forall a, b, v_a, v_b | word(a) && word(b) && encode_check_perms_cmd(a) == encode_check_perms_cmd(b)
		ensures a == b;
	{
		assert word_to_bytes(a) == word_to_bytes(b);
		lemma_word_to_bytes_unique_specific(a, b);
	}
}

lemma lemma_write_cmd_unique_general()
	ensures forall a, b, v_a, v_b :: word(a) && word(b) && 0 < |v_a| == NV_size() && 0 < |v_b| == NV_size() && encode_write_cmd(a, v_a) == encode_write_cmd(b, v_b) ==> a == b && v_a == v_b;
{
	forall a, b, v_a, v_b | word(a) && word(b) && 0 < |v_a| == NV_size() && 0 < |v_b| == NV_size() && encode_write_cmd(a, v_a) == encode_write_cmd(b, v_b)
		ensures a == b && v_a == v_b;
	{
		assert word_to_bytes(a) == word_to_bytes(b);
		lemma_word_to_bytes_unique_specific(a, b);
		assert v_a == v_b;
	}
}

lemma lemma_read_cmd_unique_general()
	ensures forall a, b :: word(a) && word(b) && encode_read_cmd(a) == encode_read_cmd(b) ==> a == b;
{
	forall a, b | word(a) && word(b) && encode_read_cmd(a) == encode_read_cmd(b)
	{
		lemma_read_cmd_unique(a, b);
	}
}

lemma lemma_read_cmd_unique(a:int, b:int)
	requires word(a) && word(b);
	requires encode_read_cmd(a) == encode_read_cmd(b);
	ensures a == b;
{
	assert word_to_bytes(a) == word_to_bytes(b);
	lemma_word_to_bytes_unique_specific(a, b);
}

ghost method lemma_check_perms_excludes_others(aTPM:TPM_struct)
	requires TPM_valid(aTPM);
	requires valid_check_perms_cmd(aTPM.cmd_buf);
	ensures !valid_read_cmd         (aTPM.cmd_buf) && 
			!valid_write_cmd		(aTPM.cmd_buf) && 
			!valid_PCR_extend_cmd	(aTPM.cmd_buf) && 
			!valid_check_locked_cmd	(aTPM.cmd_buf) && 
			!valid_quote_cmd		(aTPM.cmd_buf) &&
			!valid_get_random_cmd		(aTPM.cmd_buf) &&
			!valid_PCR_read_cmd		(aTPM.cmd_buf);
{
	assert forall a :: word(a) ==> encode_read_cmd(a)[9] != 0x65; 
	assert encode_check_locked_cmd()[13] != 0x11; 
}


ghost method lemma_check_locked_excludes_others(aTPM:TPM_struct)
	requires TPM_valid(aTPM);
	requires valid_check_locked_cmd(aTPM.cmd_buf);
	ensures !valid_read_cmd         (aTPM.cmd_buf) && 
			!valid_write_cmd		(aTPM.cmd_buf) && 
			!valid_PCR_extend_cmd	(aTPM.cmd_buf) && 
			!valid_check_perms_cmd	(aTPM.cmd_buf) && 
			!valid_quote_cmd		(aTPM.cmd_buf) &&
			!valid_get_random_cmd		(aTPM.cmd_buf) &&
			!valid_PCR_read_cmd		(aTPM.cmd_buf);
{
	assert forall a :: word(a) ==> encode_read_cmd(a)[9] != 0x65; 
	assert forall a :: word(a) ==> encode_check_perms_cmd(a)[13] != 0x04; 
}

ghost method lemma_write_excludes_others(aTPM:TPM_struct)
	requires TPM_valid(aTPM);
	requires valid_write_cmd(aTPM.cmd_buf);
	ensures !valid_read_cmd         (aTPM.cmd_buf) && 
			!valid_check_perms_cmd	(aTPM.cmd_buf) && 
			!valid_PCR_extend_cmd	(aTPM.cmd_buf) && 
			!valid_check_locked_cmd	(aTPM.cmd_buf) && 
			!valid_quote_cmd		(aTPM.cmd_buf) &&
			!valid_get_random_cmd		(aTPM.cmd_buf) &&
			!valid_PCR_read_cmd		(aTPM.cmd_buf);
{
}

ghost method lemma_read_excludes_others(aTPM:TPM_struct)
	requires TPM_valid(aTPM);
	requires valid_read_cmd(aTPM.cmd_buf);
	ensures !valid_write_cmd        (aTPM.cmd_buf) && 
			!valid_check_perms_cmd	(aTPM.cmd_buf) && 
			!valid_PCR_extend_cmd	(aTPM.cmd_buf) && 
			!valid_check_locked_cmd	(aTPM.cmd_buf) && 
			!valid_quote_cmd		(aTPM.cmd_buf) &&
			!valid_get_random_cmd		(aTPM.cmd_buf) &&
			!valid_PCR_read_cmd		(aTPM.cmd_buf);
{
	assert encode_check_locked_cmd()[13] != 0x11; 
}

ghost method lemma_read_reply_is_bytes(data:seq<int>) 
	requires is_byte_seq(data);
	requires word(|data|+14);
	ensures is_byte_seq(encode_read_reply(data));
{
	lemma_word_to_bytes_is_bytes_generic();
	assert is_byte_seq(TPM_TAG_RSP_COMMAND());
	assert is_byte_seq(word_to_bytes(|data| + 14));
	assert is_byte_seq(TPM_SUCCESS());
	assert is_byte_seq(word_to_bytes(|data|));
	assert is_byte_seq(data);
}



method hmac_unverified_impl(nonce_external:seq<int>, key_handle:seq<int>, auth_handle:seq<int>, nonce_odd:seq<int>, nonce_even:seq<int>, 
							pcr_selection:seq<int>, add_version:seq<int>, continueAuthSession:seq<int>,
							usage_key:seq<int>) returns (h:seq<int>)
	requires byte_seq(nonce_external, 20) && byte_seq(key_handle, 4) && byte_seq(auth_handle, 4) &&
	         byte_seq(nonce_odd, 20) && byte_seq(nonce_even, 20) && byte_seq(pcr_selection, 5) &&
			 byte_seq(add_version, 1) && byte_seq(continueAuthSession, 1) && byte_seq(usage_key, 20);
	ensures hmac_unverified(h, nonce_external, key_handle, auth_handle, nonce_odd, nonce_even);
{
	// First, compress the ordinal, external nonce, pcr selection, add version
	var data_byte_seq := [ 0x00, 0x00, 0x00, 0x3E ] + nonce_external + pcr_selection + add_version;
	lemma_2toX();
	var data_int_seq := byte_seq_to_word_seq(data_byte_seq);
	var data := new int[64];

	// Zero out the data array	
	var i := 0;
	while (i < data.Length) 
		invariant 0 <= i <= data.Length;
		invariant forall j :: 0 <= j < i ==> word(data[j]);
	{
		data[i] := 0;
		i := i + 1;
	}
	
	//assert forall j :: 0 <= j < data.Length ==> word(data[j]);
	copy_seq_to_array(data_int_seq, data, 0);
	var h1 := SHA1impl(data, |data_byte_seq| * 8);
	var h1_bytes := word_seq_to_byte_seq(h1[..]);
	var hmac_input := h1_bytes + nonce_even + nonce_odd + continueAuthSession;

	// Zero out the data array	
	i := 0;
	while (i < data.Length) 
		invariant 0 <= i <= data.Length;
		invariant forall j :: 0 <= j < i ==> word(data[j]);
	{
		data[i] := 0;
		i := i + 1;
	}

	data_int_seq := byte_seq_to_word_seq(hmac_input);
	copy_seq_to_array(data_int_seq, data, 0);

	var key := new int[16];
	// Zero out the key
	i := 0;
	while (i < key.Length) 
		invariant 0 <= i <= key.Length;
		invariant forall j {:trigger word(key[j])} :: 0 <= j < i ==> word(key[j]);
		invariant forall i :: 0 <= i < data.Length ==> word(data[i]);
	{
		key[i] := 0;
		i := i + 1;
	}

	var key_int_seq := byte_seq_to_word_seq(usage_key);
	copy_seq_to_array(key_int_seq, key, 0);

	var hmac := HMAC_impl(key, data, |hmac_input| * 8);

	h := word_seq_to_byte_seq(hmac[..]);
}

// Determine whether the TPM NVRAM has been properly locked
method {:timeLimit 30} check_locked() returns (r:bool)
  requires Locality3_obtained();
	requires TPM_valid(TPM);
	requires byte_seq(Verve_PCR_val, 20);
	requires TPM_satisfies_integrity_policy(TPM);
	modifies this;
	ensures r ==> TPM.NV_locked;
//
	ensures TPM_valid(TPM);
	ensures TPM_satisfies_integrity_policy(TPM);
	// Nothing else changes		
	ensures old(TPM.PCR_19)			== TPM.PCR_19;
	ensures old(TPM.NVRAM)			== TPM.NVRAM;
	ensures old(TPM.NV_locked)		== TPM.NV_locked;
	ensures old(TPM.NV_perms_ok)	== TPM.NV_perms_ok;
	ensures old(Verve_PCR_val)      == Verve_PCR_val;
{
	// Build the command:
	var cmd := [ 0x00, 0xc1, 0x00, 0x00, 0x00, 22, 0x00, 0x00, 0x00, 0x65, 0x00, 0x00, 0x00, 0x04, 0x00, 0x00, 0x00, 4, 0x00, 0x00, 0x01, 0x08];
	assert valid_check_locked_cmd(cmd);

	ghost var intermediate_TPM_1:TPM_struct := TPM_build(TPM.PCR_19, TPM.NVRAM, TPM.NV_locked, TPM.NV_perms_ok, CmdReception, cmd, [], TPM.random_index);	
	ghost var intermediate_TPM_2:TPM_struct := TPM_build(TPM.PCR_19, TPM.NVRAM, TPM.NV_locked, TPM.NV_perms_ok, Executing, cmd, [], TPM.random_index);	

	forall new_TPM | async_TPM_execution(intermediate_TPM_1, new_TPM, Verve_PCR_val) 
		ensures TPM_satisfies_integrity_policy(new_TPM);	
	{
		lemma_check_locked_excludes_others(intermediate_TPM_1);
		if (intermediate_TPM_1 != new_TPM) {
			assert TPM_check_locked(intermediate_TPM_1, new_TPM);
		}
	}

	var reply := perform_command(cmd);
	ghost var after_TPM:TPM_struct := TPM_build(TPM.PCR_19, TPM.NVRAM, TPM.NV_locked, TPM.NV_perms_ok, CmdComplete, TPM.cmd_buf, reply, TPM.random_index);
	assert async_TPM_execution(intermediate_TPM_2, after_TPM, Verve_PCR_val);

	lemma_check_locked_excludes_others(intermediate_TPM_2);
	assert TPM_check_locked(intermediate_TPM_2, after_TPM);

	if !reply_is_error(reply) {
		assert reply == encode_check_locked_reply(intermediate_TPM_2);
		var flags := reply[14..];
		assert flags == TPM_PERMANENT_FLAGS(intermediate_TPM_2);
		if reply[14..][17] == 1 {
			assert intermediate_TPM_2.NV_locked;
			return true;
		}
	}
	return false;	
}



method {:timeLimit 60} check_perms(a:int) returns (r:bool)
	requires word(a);
  requires Locality3_obtained();
	requires TPM_valid(TPM);
	requires byte_seq(Verve_PCR_val, 20);
	requires TPM_satisfies_integrity_policy(TPM);
	modifies this;
	ensures r ==> valid_nv_index(TPM, a) && TPM.NV_perms_ok[a];

	ensures TPM_valid(TPM);
	ensures TPM_satisfies_integrity_policy(TPM);
	// Nothing else changes		
	ensures old(TPM.PCR_19)			== TPM.PCR_19;
	ensures old(TPM.NVRAM)			== TPM.NVRAM;
	ensures old(TPM.NV_locked)		== TPM.NV_locked;
	ensures old(TPM.NV_perms_ok)	== TPM.NV_perms_ok;
	ensures old(Verve_PCR_val)      == Verve_PCR_val;
{
	// Build the command:
	//var a_bytes := word_2_bytes(a);
	var cmd := build_check_perms_cmd(a); //[ 0x00, 0xc1, 0x00, 0x00, 0x00, 22, 0x00, 0x00, 0x00, 0x65, 0x00, 0x00, 0x00, 0x11, 0x00, 0x00, 0x00, 4] + a_bytes;	
	//assert valid_check_perms_cmd(cmd);
	lemma_2toX();
	ghost var intermediate_TPM_1:TPM_struct := TPM_build(TPM.PCR_19, TPM.NVRAM, TPM.NV_locked, TPM.NV_perms_ok, CmdReception, cmd, [], TPM.random_index);	
	ghost var intermediate_TPM_2:TPM_struct := TPM_build(TPM.PCR_19, TPM.NVRAM, TPM.NV_locked, TPM.NV_perms_ok, Executing, cmd, [], TPM.random_index);	

	forall new_TPM | async_TPM_execution(intermediate_TPM_1, new_TPM, Verve_PCR_val) 
		ensures TPM_satisfies_integrity_policy(new_TPM);	
	{
		lemma_check_perms_excludes_others(intermediate_TPM_1);
		if (intermediate_TPM_1 != new_TPM) {
			assert TPM_check_perms(intermediate_TPM_1, new_TPM, Verve_PCR_val);
		}
	}

	var reply := perform_command(cmd);
	ghost var after_TPM:TPM_struct := TPM_build(TPM.PCR_19, TPM.NVRAM, TPM.NV_locked, TPM.NV_perms_ok, CmdComplete, TPM.cmd_buf, reply, TPM.random_index);
	assert async_TPM_execution(intermediate_TPM_2, after_TPM, Verve_PCR_val);

	lemma_check_perms_excludes_others(intermediate_TPM_2);
	assert TPM_check_perms(intermediate_TPM_2, after_TPM, Verve_PCR_val);

	var expected_reply := build_check_perms_reply(a, Verve_PCR_val, 256);

	if (expected_reply != reply ) 
	{
		return false;
	}

	assert TPM_check_perms(intermediate_TPM_2, after_TPM, Verve_PCR_val);
	assert intermediate_TPM_2.cmd_buf == encode_check_perms_cmd(a);
	assert after_TPM.reply_buf == encode_check_perms_reply(a, Verve_PCR_val, NV_size());
	lemma_check_perms_cmd_unique_general();
	assert valid_nv_index(intermediate_TPM_2, a);
	assert intermediate_TPM_2.NV_perms_ok[a];	
	return true;
}

method build_check_perms_cmd(a:int) returns (cmd:seq<int>)
	requires word(a);
	ensures cmd == encode_check_perms_cmd(a);
	ensures is_byte_seq(cmd);
{
	lemma_2toX();
	var a_bytes := word_2_bytes(a);
	cmd := [ 0x00, 0xc1, 0x00, 0x00, 0x00, 22, 0x00, 0x00, 0x00, 0x65, 0x00, 0x00, 0x00, 0x11, 0x00, 0x00, 0x00, 4] + a_bytes;	
}

method build_check_perms_reply(a:int, v:seq<int>, len:int) returns (result:seq<int>)
	requires word(a);
	requires byte_seq(v, 20);
	requires word(len);
	ensures  result == encode_check_perms_reply(a, v, len);
{	
	lemma_2toX();
	var a_bytes := word_2_bytes(a);
	var len_bytes := word_2_bytes(len);
	var verve_pcr_info := [ 0, 3, 0, 0, 6 ] + [31] + v;
	assert Verve_PCR_INFO_SHORT(v) == verve_pcr_info;
	var nv_public := [ 0, 0x18 ] + a_bytes + verve_pcr_info + verve_pcr_info + [ 0, 23 ] + [ 0, 0, 0x20, 0 ] + [0] + [0] + [0] + len_bytes;
	assert TPM_NV_DATA_PUBLIC(a, v, len) == nv_public;
	result := [ 0, 0xC4, 0, 0, 0, 85, 0, 0, 0, 0, 0, 0, 0, 71 ] + nv_public;
}

method extend_PCR(data:seq<int>) returns (r:bool)
  requires Locality3_obtained();
	requires byte_seq(data, 20);
	requires TPM_valid(TPM);
	requires byte_seq(Verve_PCR_val, 20);
	requires TPM_satisfies_integrity_policy(TPM);
	modifies this;
	ensures r ==> TPM.PCR_19 == old(TPM.PCR_19) + [data];

	ensures TPM_valid(TPM);
	ensures TPM_satisfies_integrity_policy(TPM);
	// Nothing else changes		
	ensures old(TPM.NVRAM)			== TPM.NVRAM;
	ensures old(TPM.NV_locked)		== TPM.NV_locked;
	ensures old(TPM.NV_perms_ok)	== TPM.NV_perms_ok;
	ensures old(Verve_PCR_val)      == Verve_PCR_val;
{
	// Build the command:
	var cmd := [ 0x00, 0xc1, 0x00, 0x00, 0x00, 34, 0x00, 0x00, 0x00, 0x14, 0x00, 0x00, 0x00, 19 ] + data;	

	ghost var intermediate_TPM_1:TPM_struct := TPM_build(TPM.PCR_19, TPM.NVRAM, TPM.NV_locked, TPM.NV_perms_ok, CmdReception, cmd, [], TPM.random_index);
	lemma_word_to_bytes_is_bytes_generic();
	lemma_2toX();
	var reply := perform_command(cmd);

	return !reply_is_error(reply);
}


method build_write_cmd(secret:seq<int>) returns (cmd:seq<int>)
	requires byte_seq(secret, NV_size());
	ensures word(0x00011228);
  ensures cmd == encode_write_cmd(0x00011228, secret);
  ensures is_byte_seq(cmd);
  //ensures is_byte_seq(cmd);
{
	var nvindex := 0x00011228;
	lemma_2toX();
	var nvindex_bytes := word_2_bytes(nvindex);
	cmd := [ 0x00, 0xc1, 0x00, 0x00, 0x01, 0x16, 0x00, 0x00, 0x00, 0xcd] + nvindex_bytes + [ 0, 0, 0, 0] + [ 0, 0, 1, 0] + secret;
	assert word_to_bytes(NV_size()) == [ 256 / power2(24), (256 / power2(16)) % 256, (256 / power2(8)) % 256, 256 % 256 ];
	assert [ 0, 0, 1, 0] == word_to_bytes(NV_size());
	assert  [0x00, 0x00, 0x01, 0x16] == word_to_bytes(278);
	assert  [0x00, 0x00, 0x01, 0x16] == word_to_bytes(22 + NV_size());
	/*
	assert encode_write_cmd(nvindex, secret) == [0x00, 0xc1] +
	word_to_bytes(22 + NV_size())  + // # of bytes in command, counting everything
	[0x00, 0x00, 0x00, 0xcd] +
	word_to_bytes(nvindex) + 
	[ 0, 0, 0, 0] +					// No offset
	word_to_bytes(NV_size()) +
	secret; */
	assert cmd == encode_write_cmd(0x00011228, secret);
	
}

method {:timeLimit 10} store_secret(secret:seq<int>) returns (r:bool)
  requires Locality3_obtained();
	requires byte_seq(secret, NV_size());
	requires TPM_valid(TPM);
	requires byte_seq(Verve_PCR_val, 20);
	requires TPM_satisfies_integrity_policy(TPM);
	requires TPM_app_policy_okay_to_trust(secret);
	requires valid_nv_index(TPM, 0x00011228);
	modifies this;
	ensures r ==> valid_nv_index(TPM, 0x00011228) && TPM.NVRAM[0x00011228] == secret;
	ensures forall a :: a != 0x00011228 && old(valid_nv_index(TPM, a)) && valid_nv_index(TPM, a) ==> old(TPM.NVRAM[a]) == TPM.NVRAM[a];

	ensures TPM_valid(TPM);
	ensures TPM_satisfies_integrity_policy(TPM);
	// Nothing else changes				
	ensures old(TPM.NV_locked)		== TPM.NV_locked;
	ensures old(TPM.NV_perms_ok)	== TPM.NV_perms_ok;
	ensures old(TPM.PCR_19)			== TPM.PCR_19;
	ensures old(Verve_PCR_val)      == Verve_PCR_val;	
{
	var nvindex := 0x00011228;
	var cmd := build_write_cmd(secret);

	var locked := check_locked();
	var perms_okay := check_perms(nvindex);

	if (!locked || ! perms_okay) {
		return false;
	}

    assert TPM.NV_locked;
    assert TPM.NV_perms_ok[nvindex];

	ghost var intermediate_TPM_1:TPM_struct := TPM_build(TPM.PCR_19, TPM.NVRAM, TPM.NV_locked, TPM.NV_perms_ok, CmdReception, cmd, [], TPM.random_index);
	ghost var intermediate_TPM_2:TPM_struct := TPM_build(TPM.PCR_19, TPM.NVRAM, TPM.NV_locked, TPM.NV_perms_ok, Executing, cmd, [], TPM.random_index);
  assert TPM_valid(intermediate_TPM_2);
  
	var reply := perform_command(cmd);
	ghost var after_TPM:TPM_struct := TPM_build(TPM.PCR_19, TPM.NVRAM, TPM.NV_locked, TPM.NV_perms_ok, CmdComplete, TPM.cmd_buf, reply, TPM.random_index);

	lemma_word_to_bytes_is_bytes_generic();
	lemma_2toX();
	assert valid_write_cmd(intermediate_TPM_2.cmd_buf);
	assert valid_cmd_present(intermediate_TPM_2) && intermediate_TPM_2 != after_TPM;
	assert async_TPM_execution(intermediate_TPM_2, after_TPM, Verve_PCR_val);
	assert TPM_write(intermediate_TPM_2, after_TPM);
	lemma_write_cmd_unique_general(); 
	assert intermediate_TPM_2.cmd_buf == encode_write_cmd(nvindex, secret); 

	assert forall a :: a != nvindex && valid_nv_index(intermediate_TPM_1, a) && valid_nv_index(after_TPM, a) ==> intermediate_TPM_1.NVRAM[a] == after_TPM.NVRAM[a];
    forall a:int | 0 <= a < |after_TPM.NVRAM| && after_TPM.NV_perms_ok[a]
        ensures |after_TPM.NVRAM[a]| == NV_size();
        ensures TPM_app_policy_okay_to_trust(after_TPM.NVRAM[a]) || after_TPM.NVRAM[a] == newly_created_NV_value();
    {
        assert valid_nv_index(intermediate_TPM_2, a);
        assert |intermediate_TPM_2.NVRAM[a]| == NV_size();
        assert TPM_app_policy_okay_to_trust(intermediate_TPM_2.NVRAM[a]) || intermediate_TPM_2.NVRAM[a] == newly_created_NV_value();
        assert after_TPM.NVRAM[a] == intermediate_TPM_2.NVRAM[a] || after_TPM.NVRAM[a] == secret;
    }

	if (reply_is_error(reply)) {
		return false;
	}

	assert valid_nv_index(after_TPM, nvindex) && after_TPM.NVRAM[nvindex] == secret;
	return true;
}


method {:timeLimit 50} read_secret() returns (r:bool, secret:seq<int>)
  requires Locality3_obtained();
	requires TPM_valid(TPM);
	requires byte_seq(Verve_PCR_val, 20);
	requires TPM_satisfies_integrity_policy(TPM);
	requires valid_nv_index(TPM, 0x00011228);
	modifies this;
	ensures r ==> TPM_app_policy_okay_to_trust(secret);	

	ensures TPM_valid(TPM);
	ensures TPM_satisfies_integrity_policy(TPM);
	// Nothing else changes		
	ensures old(TPM.NVRAM)			== TPM.NVRAM;
	ensures old(TPM.NV_locked)		== TPM.NV_locked;
	ensures old(TPM.NV_perms_ok)	== TPM.NV_perms_ok;
	ensures old(TPM.PCR_19)			== TPM.PCR_19;
	ensures old(Verve_PCR_val)      == Verve_PCR_val;
{
	// Build the command:
	var nvindex := 0x00011228;
	assert word(nvindex);

	var locked := check_locked();
	var perms_okay := check_perms(nvindex);

	if (!locked || ! perms_okay) {
		return false, [] ;
	}
	var nvindex_bytes := word_2_bytes(nvindex);
	var cmd := [ 0x00, 0xc1, 0x00, 0x00, 0x00, 22, 0x00, 0x00, 0x00, 0xcf ] + nvindex_bytes + [ 0, 0, 0, 0] + [ 0, 0, 1, 0];
	lemma_word_to_bytes_is_bytes_generic();
	lemma_2toX();
	assert cmd == encode_read_cmd(nvindex);

	ghost var intermediate_TPM_1:TPM_struct := TPM_build(TPM.PCR_19, TPM.NVRAM, TPM.NV_locked, TPM.NV_perms_ok, CmdReception, cmd, [], TPM.random_index);
	ghost var intermediate_TPM_2:TPM_struct := TPM_build(TPM.PCR_19, TPM.NVRAM, TPM.NV_locked, TPM.NV_perms_ok, Executing, cmd, [], TPM.random_index);

	forall new_TPM | async_TPM_execution(intermediate_TPM_1, new_TPM, Verve_PCR_val) 
		ensures TPM_satisfies_integrity_policy(new_TPM);	
	{
		lemma_read_excludes_others(intermediate_TPM_1);
		if (intermediate_TPM_1 != new_TPM) {
			assert TPM_read(intermediate_TPM_1, new_TPM);
			assert intermediate_TPM_1.cmd_buf == encode_read_cmd(nvindex);
			lemma_read_cmd_unique_general();
			lemma_read_reply_is_bytes(intermediate_TPM_1.NVRAM[nvindex]);
			assert (forall i :: 0 <= i < |new_TPM.reply_buf| ==> byte(new_TPM.reply_buf[i]));
			assert TPM_valid(new_TPM);
		}
	}

	var reply := perform_command(cmd);
	ghost var after_TPM:TPM_struct := TPM_build(TPM.PCR_19, TPM.NVRAM, TPM.NV_locked, TPM.NV_perms_ok, CmdComplete, TPM.cmd_buf, reply, TPM.random_index);
	assert async_TPM_execution(intermediate_TPM_2, after_TPM, Verve_PCR_val);
	lemma_read_excludes_others(intermediate_TPM_2);
	assert TPM_read(intermediate_TPM_2, after_TPM);

	if reply_is_error(reply) {
		return false, [];
	} 

	assert valid_nv_index(intermediate_TPM_2, nvindex);
	assert intermediate_TPM_2.cmd_buf == encode_read_cmd(nvindex);
	lemma_read_cmd_unique_general();
	assert reply == encode_read_reply(intermediate_TPM_2.NVRAM[nvindex]);

	lemma_read_reply_is_bytes(intermediate_TPM_2.NVRAM[nvindex]);
	var data := extract_read_reply_data(reply, intermediate_TPM_2.NVRAM[nvindex]);
	assert data == intermediate_TPM_2.NVRAM[nvindex];

	if (data[0] == 0xff) {
		return false, [];
	} else {
		return true, data;
	}
}

method {:timeLimit 35} quote(nonce_external:seq<int>, key_handle:int, auth_handle:int, nonce_even:seq<int>, usage_key:seq<int>) returns (r:bool, q:seq<int>)
  requires Locality3_obtained();
	requires byte_seq(nonce_external, 20) && word(key_handle) && word(auth_handle) && word_seq(nonce_even, 5) && word_seq(usage_key, 5);
	//requires byte_seq(nonce_external, 20) && byte_seq(key_handle, 4) && byte_seq(auth_handle, 4) && byte_seq(nonce_even, 20) && byte_seq(usage_key, 20);
	requires TPM_valid(TPM);
	requires byte_seq(Verve_PCR_val, 20);
	requires TPM_satisfies_integrity_policy(TPM);
	modifies this;

	ensures r ==> Verve_quote(q, nonce_external, old(TPM).PCR_19);

	ensures TPM_valid(TPM);
	ensures TPM_satisfies_integrity_policy(TPM);
	// Nothing else changes		
	ensures old(TPM.NVRAM)			== TPM.NVRAM;
	ensures old(TPM.NV_locked)		== TPM.NV_locked;
	ensures old(TPM.NV_perms_ok)	== TPM.NV_perms_ok;
	ensures old(TPM.PCR_19)			== TPM.PCR_19;
	ensures old(Verve_PCR_val)      == Verve_PCR_val;
{
	// Build the command:
	var pcr_selection := [ 0x00, 0x03, 0x00, 0x00, 0x0E ];
	var nonce_odd_bytes := [ 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 
							 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00 ];
	var nonce_external_bytes := nonce_external; // word_seq_to_byte_seq(nonce_external);	
	var nonce_even_bytes := word_seq_to_byte_seq(nonce_even);
	var usage_key_bytes := word_seq_to_byte_seq(usage_key);
	var key_handle_bytes := word_2_bytes(key_handle);
	var auth_handle_bytes := word_2_bytes(auth_handle);

	lemma_2toX();
	var auth_data := hmac_unverified_impl(nonce_external_bytes, key_handle_bytes, auth_handle_bytes, nonce_odd_bytes, nonce_even_bytes, pcr_selection, [ 1 ], [ 1 ], usage_key_bytes); 
	var cmd := [ 0x00, 0xc2, 0x00, 0x00, 0x00, 85, 0x00, 0x00, 0x00, 0x3e ] +
				key_handle_bytes + 
				nonce_external_bytes +
				pcr_selection + 
				[ 1 ] +
				auth_handle_bytes +
				nonce_odd_bytes +
				[ 1 ] +
				auth_data;

	//assert hmac_unverified(auth_data, nonce_external, key_handle, auth_handle, nonce_odd, nonce_even);
	assert cmd == encode_quote_cmd(auth_data, nonce_external_bytes, key_handle_bytes, auth_handle_bytes, nonce_odd_bytes, nonce_even_bytes);

	ghost var intermediate_TPM_1:TPM_struct := TPM_build(TPM.PCR_19, TPM.NVRAM, TPM.NV_locked, TPM.NV_perms_ok, CmdReception, cmd, [], TPM.random_index);

	forall new_TPM | async_TPM_execution(intermediate_TPM_1, new_TPM, Verve_PCR_val) 
		ensures TPM_satisfies_integrity_policy(new_TPM);
	{	
		assert intermediate_TPM_1.NVRAM == new_TPM.NVRAM;		
	}

	q := perform_command(cmd);

	return !reply_is_error(q), q;
}
