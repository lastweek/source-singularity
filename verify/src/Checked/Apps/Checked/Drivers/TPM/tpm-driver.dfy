include "..\..\..\Trusted\Spec\TPM\tpm-device.dfy"
include "..\..\Libraries\Math\mul.dfy"
include "..\..\Libraries\Math\div.dfy"
include "..\..\Libraries\Math\power2.dfy"
include "..\..\Libraries\Util\arrays_and_seqs.dfy"

/***************************************************************************
 *	             LOW-LEVEL TPM INTERACTION 
 ***************************************************************************/

method establish_locality() 
  ensures Locality3_obtained();
{
  request_access();

  lemma_2toX();

  var done := false;
  while(!done) 
    decreases *;
    invariant Locality3_requested();
    invariant done ==> Locality3_obtained();
  {
    var status := check_access_status();
    status := BitwiseAndInstruction(status, 32);
    if status > 0 {
      done := true;
    }
  }
}


method {:timeLimit 40} perform_command(command_bytes:seq<int>) returns (reply_bytes:seq<int>)
  requires Locality3_obtained();
	requires TPM_valid(TPM);
	requires byte_seq(Verve_PCR_val, 20);
	requires byte_seq(command_bytes, |command_bytes|);
	requires |command_bytes| >= 1;
	requires valid_cmd(command_bytes);
	requires var intermediate_TPM_1:TPM_struct := TPM_build(TPM.PCR_19, TPM.NVRAM, TPM.NV_locked, TPM.NV_perms_ok, CmdReception, command_bytes, [], TPM.random_index);
             (forall new_TPM : TPM_struct :: (async_TPM_execution(intermediate_TPM_1, new_TPM, Verve_PCR_val) ==> TPM_satisfies_integrity_policy(new_TPM)));	
	modifies this;
	ensures old(Verve_PCR_val)      == Verve_PCR_val;
	ensures var intermediate_TPM_2:TPM_struct := TPM_build(old(TPM).PCR_19, old(TPM).NVRAM, old(TPM).NV_locked, old(TPM).NV_perms_ok, Executing, command_bytes, [], old(TPM).random_index);
            var intermediate_TPM_3:TPM_struct := TPM_build(TPM.PCR_19, TPM.NVRAM, TPM.NV_locked, TPM.NV_perms_ok, CmdComplete, TPM.cmd_buf, reply_bytes, TPM.random_index);
            async_TPM_execution(intermediate_TPM_2, intermediate_TPM_3, Verve_PCR_val);
	ensures TPM_valid(TPM);
	ensures TPM.cmd_state.CmdComplete?;
{
	ghost var intermediate_TPM_1:TPM_struct := TPM_build(TPM.PCR_19, TPM.NVRAM, TPM.NV_locked, TPM.NV_perms_ok, CmdReception, command_bytes, [], TPM.random_index);
	ghost var intermediate_TPM_2:TPM_struct := TPM_build(TPM.PCR_19, TPM.NVRAM, TPM.NV_locked, TPM.NV_perms_ok, Executing, command_bytes, [], TPM.random_index);

	send_command(command_bytes);
	assert TPM.cmd_buf == command_bytes;
	assert TPM == intermediate_TPM_1;

	execute_command();
    assert TPM.cmd_state == Executing;
    assert TPM == intermediate_TPM_2;

	poll_data_available();

	ghost var intermediate_TPM_3:TPM_struct := TPM;
	assert byte_seq(Verve_PCR_val, 20);
	assert TPM_valid(intermediate_TPM_2);
	assert async_TPM_execution(intermediate_TPM_2, intermediate_TPM_3, Verve_PCR_val);

	reply_bytes := retrieve_response();
    assert intermediate_TPM_3.reply_buf == reply_bytes;
    assert intermediate_TPM_3 == TPM_build(TPM.PCR_19, TPM.NVRAM, TPM.NV_locked, TPM.NV_perms_ok, CmdComplete, TPM.cmd_buf, reply_bytes, TPM.random_index);
    assert async_TPM_execution(intermediate_TPM_2, intermediate_TPM_3, Verve_PCR_val);
    assert command_bytes == old(command_bytes);
    //assert intermediate_TPM_2 == TPM_build(old(TPM).PCR_19, old(TPM).NVRAM, old(TPM).NV_locked, old(TPM).NV_perms_ok, Executing, command_bytes, [], old(TPM).random_index);
    //assert var f_intermediate_TPM_2:TPM_struct := TPM_build(old(TPM).PCR_19, old(TPM).NVRAM, old(TPM).NV_locked, old(TPM).NV_perms_ok, Executing, command_bytes, [], old(TPM).random_index);
    //        var f_intermediate_TPM_3:TPM_struct := TPM_build(TPM.PCR_19, TPM.NVRAM, TPM.NV_locked, TPM.NV_perms_ok, CmdComplete, TPM.cmd_buf, reply_bytes, TPM.random_index);
    //        f_intermediate_TPM_2 == intermediate_TPM_2 && f_intermediate_TPM_3 == intermediate_TPM_3 &&
    //        async_TPM_execution(f_intermediate_TPM_2, f_intermediate_TPM_3, Verve_PCR_val);
}

method {:timeLimit 31} send_command(command_bytes:seq<int>) 
  requires Locality3_obtained();
	requires TPM_valid(TPM);
	requires byte_seq(Verve_PCR_val, 20);
	requires byte_seq(command_bytes, |command_bytes|);
	requires |command_bytes| >= 1;
	requires valid_cmd(command_bytes);
	modifies this;
	ensures TPM.cmd_buf == command_bytes[..];
	ensures TPM.cmd_state.CmdReception?;
	ensures TPM.reply_buf == [];
	ensures TPM_valid(TPM);
	// Nothing else changes
	ensures old(TPM.PCR_19)			== TPM.PCR_19;
	ensures old(TPM.NVRAM)			== TPM.NVRAM;
	ensures old(TPM.NV_locked)		== TPM.NV_locked;
	ensures old(TPM.NV_perms_ok)	== TPM.NV_perms_ok;
  ensures old(Verve_PCR_val)      == Verve_PCR_val;	
  ensures old(TPM.random_index) == TPM.random_index;
{
	assert TPM.cmd_state.Idle? || TPM.cmd_state.Ready? || TPM.cmd_state.CmdReception? || TPM.cmd_state.Executing? || TPM.cmd_state.CmdComplete?;	
	issue_command_ready();
	issue_command_ready();
	assert TPM.cmd_state.Ready?;

	// Write one byte to move us into CmdReception
	write_FIFO(command_bytes[0]);

	var i := 1;
	while (i < |command_bytes|) 
		invariant TPM.cmd_state.CmdReception?;
		invariant TPM_valid(TPM);
		invariant byte_seq(Verve_PCR_val, 20);
		invariant 1 <= i <= |command_bytes|;
		invariant TPM.cmd_buf == command_bytes[0..i];
		invariant TPM.reply_buf == [];
		// Nothing else in the TPM changes
		invariant old(TPM.PCR_19)			== TPM.PCR_19;
		invariant old(TPM.NVRAM)			== TPM.NVRAM;
		invariant old(TPM.NV_locked)		== TPM.NV_locked;
		invariant old(TPM.NV_perms_ok)		== TPM.NV_perms_ok;
		invariant old(Verve_PCR_val)		== Verve_PCR_val;
		invariant TPM_valid(TPM);
    invariant old(TPM.random_index) == TPM.random_index;
	{
		write_FIFO(command_bytes[i]);
		i := i + 1;
	}

}


method execute_command()
  requires Locality3_obtained();
	requires TPM_valid(TPM);
	requires byte_seq(Verve_PCR_val, 20);
	requires TPM.cmd_state.CmdReception?;
	requires valid_cmd_present(TPM);
	requires forall new_TPM : TPM_struct :: async_TPM_execution(TPM, new_TPM, Verve_PCR_val) ==> TPM_satisfies_integrity_policy(new_TPM);
	modifies this;
	ensures TPM.cmd_state.Executing?;
	// Nothing else changes
	ensures old(TPM.PCR_19)			== TPM.PCR_19;
	ensures old(TPM.NVRAM)			== TPM.NVRAM;
	ensures old(TPM.NV_locked)		== TPM.NV_locked;
	ensures old(TPM.NV_perms_ok)	== TPM.NV_perms_ok;
	ensures old(TPM.cmd_buf)		== TPM.cmd_buf;
	ensures old(TPM.reply_buf)		== TPM.reply_buf;
	ensures old(Verve_PCR_val)      == Verve_PCR_val;
  ensures old(TPM.random_index) == TPM.random_index;
	ensures valid_cmd_present(TPM);
{
	go();	
}


method poll_data_available()
  requires Locality3_obtained();
	requires TPM_valid(TPM);
	requires byte_seq(Verve_PCR_val, 20);
	requires TPM.cmd_state.Executing?;
	requires valid_cmd_present(TPM);
	modifies this;
	ensures TPM_valid(TPM);	
	ensures valid_cmd_present(TPM);
	ensures TPM.cmd_state.CmdComplete?;
	ensures |TPM.reply_buf| > 0;
	ensures old(Verve_PCR_val)      == Verve_PCR_val;
	ensures async_TPM_execution(old(TPM), TPM, Verve_PCR_val);
	// Nothing else changes	
	ensures old(TPM.NV_locked)		== TPM.NV_locked;
	ensures old(TPM.NV_perms_ok)	== TPM.NV_perms_ok;
	ensures old(TPM.cmd_buf)		== TPM.cmd_buf;	
{
	var r := check_data_available_wrapper();
	while (r != 0x90) 
		invariant TPM_valid(TPM);
		invariant byte_seq(Verve_PCR_val, 20);
		invariant valid_cmd_present(TPM);
		invariant TPM.cmd_state.CmdComplete? || TPM.cmd_state.Executing?;
		invariant r == 0x90 ==> TPM.cmd_state.CmdComplete?;
		invariant r == 0x90 ==> |TPM.reply_buf| > 0;
		invariant old(TPM.cmd_state.Executing?)		==> byte_seq(Verve_PCR_val, 20) &&	// Doesn't change hash's validity
													async_TPM_execution(old(TPM), TPM, Verve_PCR_val) &&  // May bump us to CmdComplete, or may leave us in Executing
												    (r == 0x90 <==> TPM.cmd_state.CmdComplete?);		// 0x90 = TIS_STS_VALID (0x80) + TIS_STS_DATA_AVAIL (0x10)
		decreases *;
		// Nothing else changes	
		invariant old(TPM.NV_locked)		== TPM.NV_locked;
		invariant old(TPM.NV_perms_ok)		== TPM.NV_perms_ok;
		invariant old(TPM.cmd_buf)			== TPM.cmd_buf;
		invariant old(Verve_PCR_val)		== Verve_PCR_val;
	{
		r := check_data_available_wrapper();
	}
}


method {:timeLimit 40} retrieve_response() returns (ret:seq<int>)
  requires Locality3_obtained();
	requires TPM_valid(TPM);
	requires byte_seq(Verve_PCR_val, 20);
	requires TPM.cmd_state.CmdComplete?;
	requires valid_cmd_present(TPM);
	requires |TPM.reply_buf| > 0;
	modifies this;
	ensures TPM_valid(TPM);
	ensures valid_cmd_present(TPM);
	ensures ret == old(TPM).reply_buf;
	ensures TPM.reply_buf == [];
	ensures TPM.cmd_state.CmdComplete?;	
	// Nothing else changes	
	ensures old(TPM.PCR_19)			== TPM.PCR_19;
	ensures old(TPM.NVRAM)			== TPM.NVRAM;
	ensures old(TPM.NV_locked)		== TPM.NV_locked;
	ensures old(TPM.NV_perms_ok)	== TPM.NV_perms_ok;
	ensures old(TPM.cmd_buf)		== TPM.cmd_buf;
	ensures old(Verve_PCR_val)      == Verve_PCR_val;
  ensures old(TPM.random_index)			== TPM.random_index;
{
	var r := check_data_available_wrapper();

	ret := [];
	while (r == 0x90) 
		invariant TPM_valid(TPM);
		invariant byte_seq(Verve_PCR_val, 20);
		invariant valid_cmd_present(TPM);
		invariant TPM.cmd_state.CmdComplete?;
		invariant r == 0x90 <==> |TPM.reply_buf| > 0;		
		invariant ret + TPM.reply_buf == old(TPM.reply_buf);	
		decreases *;
		// Nothing else changes	
		invariant old(TPM.PCR_19)			== TPM.PCR_19;
		invariant old(TPM.NVRAM)			== TPM.NVRAM;
		invariant old(TPM.NV_locked)		== TPM.NV_locked;
		invariant old(TPM.NV_perms_ok)		== TPM.NV_perms_ok;
		invariant old(TPM.cmd_buf)			== TPM.cmd_buf;
		invariant old(Verve_PCR_val)		== Verve_PCR_val;
    invariant old(TPM.random_index)			== TPM.random_index;
	{
    ghost var old_reply_buff := TPM.reply_buf;
    ghost var old_ret := ret;
    assert old_ret + old_reply_buff == old(TPM.reply_buf);
		var c := read_FIFO();
    assert [c] + TPM.reply_buf == old_reply_buff; 
		ret := ret + [c];
    assert ret == old_ret + [c];
    calc {
      ret + TPM.reply_buf;
      old_ret + [c] + TPM.reply_buf;
      old_ret + ([c] + TPM.reply_buf);
      old_ret + old_reply_buff;
      old(TPM.reply_buf);
    }
		r := check_data_available_wrapper();
	}
}


method {:timeLimit 30} check_data_available_wrapper() returns (r:int)
  requires Locality3_obtained();
	requires TPM_valid(TPM);
	requires byte_seq(Verve_PCR_val, 20);
	requires TPM.cmd_state.CmdComplete? || TPM.cmd_state.Executing?;
	requires valid_cmd_present(TPM);
	modifies this;
	ensures TPM_valid(TPM);
	ensures r == 0x90 ==> TPM.cmd_state.CmdComplete?;
	ensures r == 0x90 ==> |TPM.reply_buf| > 0;
	ensures TPM.cmd_state.CmdComplete? || TPM.cmd_state.Executing?;
	ensures  old(TPM.cmd_state.Executing?)		==> byte_seq(Verve_PCR_val, 20) &&	// Doesn't change hash's validity
													async_TPM_execution(old(TPM), TPM, Verve_PCR_val) &&  // May bump us to CmdComplete, or may leave us in Executing
												    (r == 0x90 <==> TPM.cmd_state.CmdComplete?);		// 0x90 = TIS_STS_VALID (0x80) + TIS_STS_DATA_AVAIL (0x10)
	ensures old(TPM.cmd_state.CmdComplete?) ==> (r == 0x90 <==> |TPM.reply_buf| > 0) && old(TPM) == TPM;
	// Nothing else changes	
	ensures old(TPM.NV_locked)		== TPM.NV_locked;
	ensures old(TPM.NV_perms_ok)	== TPM.NV_perms_ok;
	ensures old(TPM.cmd_buf)		== TPM.cmd_buf;
	ensures old(Verve_PCR_val)      == Verve_PCR_val;
	ensures valid_cmd_present(TPM);
{
	r := check_data_available();

	assert old(TPM.cmd_state.Executing?) && r == 0x90 ==> TPM.cmd_state.CmdComplete?;
	assert old(TPM.cmd_state.CmdComplete?) ==> TPM.cmd_state.CmdComplete?;

	// Prove that the TPM and cmd_buf remain valid
	if TPM_read(old(TPM), TPM) {
		read_reply_is_byte_seq(old(TPM));
		assert TPM_valid(TPM);
		assert old(TPM.cmd_buf)		== TPM.cmd_buf;
		assert (exists a:int ::
				word(a) &&
				old(TPM).cmd_buf == encode_read_cmd(a));
		ghost var a :| word(a) && old(TPM).cmd_buf == encode_read_cmd(a);
		assert word(a) && TPM.cmd_buf == encode_read_cmd(a);
		assert valid_cmd_present(TPM);
		assert r == 0x90 ==> |TPM.reply_buf| > 0;
	} else if TPM_write(old(TPM), TPM) {
		assert TPM_valid(TPM);
		assert old(TPM.cmd_buf)		== TPM.cmd_buf;
		assert exists a:int, v:seq<int> :: word(a) && 0 < |v| == NV_size() && old(TPM.cmd_buf)	 == encode_write_cmd(a, v); 
	} else if TPM_extend(old(TPM), TPM) {
		assert TPM_valid(TPM);
		assert old(TPM.cmd_buf)		== TPM.cmd_buf;
		assert exists data:seq<int> :: byte_seq(data, 20) && old(TPM.cmd_buf) == encode_PCR_extend_cmd(data);
		assert valid_cmd_present(TPM);
		assert r == 0x90 ==> |TPM.reply_buf| > 0;
	} else if TPM_check_perms(old(TPM), TPM, Verve_PCR_val) {
		assert TPM_valid(TPM);
		assert old(TPM.cmd_buf)		== TPM.cmd_buf;
		assert exists a:int :: word(a) && old(TPM).cmd_buf   == encode_check_perms_cmd(a);
		ghost var a :| word(a) && old(TPM).cmd_buf   == encode_check_perms_cmd(a);
		assert  word(a) && TPM.cmd_buf   == encode_check_perms_cmd(a);
		assert valid_cmd_present(TPM);
		assert r == 0x90 ==> |TPM.reply_buf| > 0;
	} else if TPM_check_locked(old(TPM), TPM) {
		check_locked_is_byte_seq(old(TPM));
		assert TPM_valid(TPM);
		assert valid_cmd_present(TPM);
		assert r == 0x90 ==> |TPM.reply_buf| > 0;
	} else if TPM_quote(old(TPM), TPM) {
		assert TPM_valid(TPM);
		assert valid_cmd_present(TPM);
		assert r == 0x90 ==> |TPM.reply_buf| > 0;
	} else if TPM_get_random(old(TPM), TPM) {
    if(is_error_reply(TPM.reply_buf)) {
      assert is_byte_seq(TPM.reply_buf);
    } else {
      random_reply_is_byte_seq(TPM);
    //  assert is_byte_seq(TPM.reply_buf);
    //
    //  assert 	|TPM.NVRAM| == |TPM.NV_perms_ok| && 
	  // word(|TPM.NVRAM|) &&	
	  //(forall i :: 0 <= i < |TPM.PCR_19| ==> byte_seq(TPM.PCR_19[i], 20)) &&	// Must be sets of 20 bytes
	  //(forall i :: 0 <= i < |TPM.cmd_buf|   ==> byte(TPM.cmd_buf[i])) &&
	  //(forall i :: 0 <= i < |TPM.reply_buf| ==> byte(TPM.reply_buf[i])) &&
	  //(forall a :: valid_nv_index(TPM, a) ==> word(|TPM.NVRAM[a]|+14) && is_byte_seq(TPM.NVRAM[a]))	;
      assert TPM_valid(TPM);
      assert valid_cmd_present(TPM);
    }
  } else if TPM_PCR_read(old(TPM), TPM) {
    get_pcr_reply_is_byte_seq(TPM);
  //assert 	|TPM.NVRAM| == |TPM.NV_perms_ok| && 
	// word(|TPM.NVRAM|) &&	
	//(forall i :: 0 <= i < |TPM.PCR_19| ==> byte_seq(TPM.PCR_19[i], 20)) &&	// Must be sets of 20 bytes
	//(forall i :: 0 <= i < |TPM.cmd_buf|   ==> byte(TPM.cmd_buf[i])) &&
	//(forall i :: 0 <= i < |TPM.reply_buf| ==> byte(TPM.reply_buf[i])) &&
	//(forall a :: valid_nv_index(TPM, a) ==> word(|TPM.NVRAM[a]|+14) && is_byte_seq(TPM.NVRAM[a]))	;
   assert TPM_valid(TPM);
   assert valid_cmd_present(TPM);
  }
	
	assert TPM_valid(TPM);
}

lemma random_reply_is_byte_seq(aTPM:TPM_struct)
  ensures forall rand_bytes:seq<int> :: is_byte_seq(rand_bytes) && word(|rand_bytes|+14) ==> is_byte_seq(encode_get_random_reply(rand_bytes));
{
  lemma_word_to_bytes_is_bytes_generic();
}

lemma get_pcr_reply_is_byte_seq(aTPM:TPM_struct)
  ensures word(30);
  ensures forall rand_bytes:seq<int> :: is_byte_seq(rand_bytes) && |rand_bytes| == 20 ==> is_byte_seq(encode_pcr_read_reply(rand_bytes));
{
  lemma_2toX();
  assert word(30);
  lemma_word_to_bytes_is_bytes_generic();
}


lemma read_reply_is_byte_seq(aTPM:TPM_struct)
	requires TPM_valid(aTPM);
	ensures forall a:int :: valid_nv_index(aTPM, a) ==> is_byte_seq(encode_read_reply(aTPM.NVRAM[a]));
{
	lemma_word_to_bytes_is_bytes_generic();
}

lemma check_locked_is_byte_seq(aTPM:TPM_struct)
	requires TPM_valid(aTPM);
	ensures  is_byte_seq(encode_check_locked_reply(aTPM));
{
	lemma_word_to_bytes_is_bytes_generic();
	lemma_2toX();	
}


