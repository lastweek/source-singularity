include "../../../../Trusted/Spec/Assembly.dfy"
include "../../../../Trusted/Spec/Libraries/Math/power2.dfy"
include "../../../../Trusted/Spec/Libraries/Util/arrays_and_seqs.dfy"
include "../../../Libraries/Math/power2.dfy"
//include "../../../Libraries/Math/mul.dfy"
include "../../../Libraries/Math/div.dfy"
include "../../../../Trusted/Spec/Libraries/Util/relational.dfy"

/**************************************************
 * Spec for interacting with the network card 
 **************************************************/
// Dafny's version of a constant
function intel_NIC_device_vendor_id() : int { 0x107c8086 }

// Track whether we've initialized the network card
var net_init:bool;

function IsValidPciId(id:int):bool
function PciMemAddr(id:int):int     // Region where the device's PCI config registers are mapped into memory
function PciMemSize(id:int):int
function DeviceMemAddr() : int      // Region where devices are allowed to read/write
function DeviceMemSize() : int

/****************************************
   Connections to Verve's PCI interface
 ****************************************/
method {:axiom} NetworkPciMemSetup() returns (id:int, size:int, addr:int, device_mem_addr:int)
  ensures word(size) && word(addr) && word(device_mem_addr);
  ensures IsValidPciId(id);
  ensures size == PciMemSize(id);
  ensures addr == PciMemAddr(id);
  ensures addr % 4 == 0;
  ensures word(addr + size);
  ensures word(DeviceMemAddr() + DeviceMemSize());
  ensures DeviceMemAddr() == device_mem_addr;
  ensures device_mem_addr % 16 == 0;
  ensures DeviceMemSize() > 0x204000;

method {:axiom} PciMemStore(id:int, dst:int, val:int)
  requires left(id) == right(id);
  requires left(dst) == right(dst);
  requires left(val) == right(val);
  requires IsValidPciId(id);
  requires PciMemAddr(id) <= dst < PciMemAddr(id) + PciMemSize(id);
  requires dst % 4 == 0;
  requires word(val);

method {:axiom} PciMemLoad(id:int, src:int) returns (val:int)
  requires left(id) == right(id);
  requires left(src) == right(src);
  requires IsValidPciId(id);
  requires PciMemAddr(id) <= src < PciMemAddr(id) + PciMemSize(id);
  requires src % 4 == 0;
  ensures word(val);

method {:axiom} DeviceMemStore(dst:int, val:int, ghost send_auth_word:bool, ghost auth_word_index:int, ghost packet:seq<int>)
  requires left(send_auth_word)  == right(send_auth_word);
  requires left(auth_word_index) == right(auth_word_index);
  requires !send_auth_word ==> left(dst) == right(dst) && left(val) == right(val);
  requires send_auth_word ==> 0 <= auth_word_index < |packet| <= 375
           && app_approves_disclosure(left(packet), right(packet), 375)
           &&  left(packet)[auth_word_index] == val
           && right(packet)[auth_word_index] == val;
  requires DeviceMemAddr() <= dst < DeviceMemAddr() + DeviceMemSize();
  requires word(dst);
  requires word(val);

method {:axiom} DeviceMemLoad(src:int) returns (val:int)
  requires left(src) == right(src);
  requires DeviceMemAddr() <= src < DeviceMemAddr() + DeviceMemSize();
  requires word(src);
  ensures word(val);

/****************************************
   Dafny "constants"
 ****************************************/

function method register_ctrl(addr:int):int					{ addr + 0x0000 }
function method register_status(addr:int):int				{ addr + 0x0004 }
function method register_mta_register(addr:int):int			{ addr + 0x5200 }
function method register_fcal(addr:int):int					{ addr + 0x0028 }
function method register_fcah(addr:int):int					{ addr + 0x002c }
function method register_fct(addr:int):int					{ addr + 0x0030 }
function method register_fcttv(addr:int):int				{ addr + 0x0170 }
function method register_ral0(addr:int):int					{ addr + 0x5400 }
function method register_rah0(addr:int):int					{ addr + 0x5404 }
function method register_rx_desc_base_lo(addr:int):int		{ addr + 0x2800 }
function method register_rx_desc_base_hi(addr:int):int		{ addr + 0x2804 }
function method register_rx_desc_length(addr:int):int		{ addr + 0x2808 }
function method register_rx_desc_head(addr:int):int			{ addr + 0x2810 }
function method register_rx_desc_tail(addr:int):int			{ addr + 0x2818 }
function method register_rx_ctrl(addr:int):int				{ addr + 0x0100 }
function method register_rx_delay_timer(addr:int):int		{ addr + 0x2820 }
function method register_rx_int_abs_timer(addr:int):int		{ addr + 0x282c }
function method register_rx_checksum(addr:int):int			{ addr + 0x5000 }
function method register_tx_desc_base_lo(addr:int):int		{ addr + 0x3800 }
function method register_tx_desc_base_hi(addr:int):int		{ addr + 0x3804 }
function method register_tx_desc_length(addr:int):int		{ addr + 0x3808 }
function method register_tx_desc_head(addr:int):int			{ addr + 0x3810 }
function method register_tx_desc_tail(addr:int):int			{ addr + 0x3818 }
function method register_tx_ctrl(addr:int):int				{ addr + 0x0400 }
function method register_tx_ipg(addr:int):int				{ addr + 0x0410 }
//function method register_(addr:int):int					{ addr + 0x000? }

function method tx_default_ipg():int { 10 }
function method ctrl_rx_enable():int { 2 } // == 1u << 1
function method ctrl_tx_enable():int { 2 } // == 1u << 1
function method ctrl_reset():int	 { 0x04000000 } // ==  1u << 26
function method ctrl_phy_reset():int { 0x80000000 } // ==  1u << 31
function method rxdelaytimers_rx_delay_timer():int		{ 100 }  // ~100us
function method rxdelaytimers_rx_absolute_timer():int	{ 1000 } // ~1000us

function method num_descriptors():int { 512 }
function method bytes_per_descriptor():int { 16 }
function method bytes_per_buffer():int { 2*1024 }
function method total_desc_bytes():int { 512 * bytes_per_descriptor() }
function method total_buffer_bytes():int { 512 * bytes_per_buffer() }

// Hard code the MAC address to d4-85-64-c3-19-f6
function method my_ethernet_addr() : ethernet_addr 
{
	ethernet_addr_builder( [ 0xd4, 0x85, 0x64, 0xc3, 0x19, 0xf6] )
}

//function method my_ethernet_addr_lo():int { 0x64c319f6 }
//function method my_ethernet_addr_hi():int { 0xd485 }

datatype ethernet_addr = ethernet_addr_builder(bytes:seq<int>);
function valid_ethernet_addr(addr:ethernet_addr) : bool
{
	byte_seq(addr.bytes, 6)
}

//////////// TODO: Update to point at Jon's functions!
method {:axiom} little_endian_bytes_to_word(bytes:seq<int>) returns (w:int)
	requires is_byte_seq(bytes);
	requires |bytes| <= 4;
	ensures word(w);

/****************************************
   Setup code -- correct by fiat
 ****************************************/
/*
 * Memory layout plan: Verve gives us, via NetworkPciMemSetup, an address in device memory
 * That memory is untrusted, but accessible to devices.  We will lay it out as follows:
 *	+1M
 *  			Rx Buffers x 512 (2K each)
 *  +8K
 *				Rx Ring Descriptors x 512 (16B each)
 *  +1M
 *  			Tx Buffers x 512 (2K each)
 *  +8K 
 *				Tx Ring Descriptors x 512 (16B each)
 *  dev_addr->  
 *
 * Thus, we need 2M+16K bytes = 0x204000
 */
method {:timeLimit 35} init_network_card() returns (b:bool, rx_ring_buff:ring_buffer, tx_ring_buff:ring_buffer)
	requires !net_init;
	modifies this;
	ensures b ==> net_init;
	ensures b ==> valid_ring_buffer(rx_ring_buff);
	ensures b ==> valid_ring_buffer(tx_ring_buff);
{
	var id, size, addr, dev_addr := NetworkPciMemSetup();
	
	if (size < 128*1024) {	// We expect the IntelNIC to get 128K worth of PCI config space mapped into memory
		b := false;	
	} else {
		assert 512 == num_descriptors();	// Used 512 in code to avoid issues with INTERNAL_mul()
		var tx_desc_base_lo	:= dev_addr;
		var tx_desc_len 	:= total_desc_bytes();
		var tx_desc_head  	:= 0;	
		var tx_desc_tail 	:= 0;		// tail == head ==> queue is empty (Sec. 3.4) ==> no packets to transmit

		var rx_desc_base_lo := dev_addr + total_desc_bytes() + total_buffer_bytes(); 
		var rx_desc_len 	:= total_desc_bytes();
		var rx_desc_head  	:= 0;	
		var rx_desc_tail 	:= num_descriptors()-1;   // Hardware owns all but the last receive descriptor, so we're open for business

		assert(rx_desc_base_lo == dev_addr + 512*16 + 512*2*1024);
		
		lemma_2toX();
		assert rx_desc_base_lo % 16 == 0;
		assert tx_desc_base_lo % 16 == 0;
		assert rx_desc_len % 128 == 0 && 128 <= rx_desc_len < power2(19);
		assert rx_desc_head < power2(16);
		assert rx_desc_tail < power2(16);

		assert tx_desc_base_lo % 16 == 0;
		assert tx_desc_base_lo % 16 == 0;
		assert tx_desc_len % 128 == 0 && 128 <= tx_desc_len < power2(19);
		assert tx_desc_head < power2(16);
		assert tx_desc_tail < power2(16);

		// Reset the card
		var temp_reg := PciMemLoad(id, register_ctrl(addr));
		temp_reg := BitwiseOrInstruction(temp_reg, ctrl_reset());
		temp_reg := BitwiseOrInstruction(temp_reg, ctrl_phy_reset());
		PciMemStore(id, register_ctrl(addr), temp_reg);

		// Wait 3us for the board to quiesce
		var count := 0;
		while (count < 9000*100)//9K ops should be ~3us on a 3GHz machine; include some margin
			decreases 9000*100 - count;
		{
			count := count + 1;
		}

		// Set the control register to values we want
		PciMemStore(id, register_ctrl(addr), 0x61); 
	// 				Flags value above corresponds to:
	//				   ctrl_fd() |  	// 1u << 0
	//				   ctrl_asde() | 	// 1u << 5
	//				   ctrl_slu());		// 1u << 6

		// Setup the physical network controls
		// Don't think we need this -- for the 8254PI, these bits are reserved and set to 00b
		//PciMemStore(id, register_ctrl_ext(addr), ctrl_ext_link_mode_phys() | 

		// Turn off flow control
		PciMemStore(id, register_fcal(addr),	0);
		PciMemStore(id, register_fcah(addr),	0);
		PciMemStore(id, register_fct(addr),	 	0);
		PciMemStore(id, register_fcttv(addr),	0);

		// Setup the MAC address 
		var mac_addr := my_ethernet_addr();
		var addr_lo := little_endian_bytes_to_word(mac_addr.bytes[0..4]);
		var addr_hi := little_endian_bytes_to_word(mac_addr.bytes[4..6]);
		PciMemStore(id, register_ral0(addr), addr_lo);
		temp_reg := addr_hi;
		temp_reg := BitwiseOrInstruction(temp_reg, 0x80000000); // Set the Address Valid bit
		PciMemStore(id, register_rah0(addr), temp_reg); 

		// Clear the multicast table
		var mta_register := 0;
		while (mta_register < 128) 
		{
			PciMemStore(id, register_mta_register(addr) + mta_register*4, 0);
			mta_register := mta_register + 1;
		}

		// Setup Descriptor buffers for rx
		PciMemStore(id, register_rx_desc_base_lo(addr),	rx_desc_base_lo);
		PciMemStore(id, register_rx_desc_base_hi(addr),	0);
		PciMemStore(id, register_rx_desc_length(addr), 	rx_desc_len);
		PciMemStore(id, register_rx_desc_head(addr),	rx_desc_head);
    assert left(rx_desc_tail) == right(rx_desc_tail);
		PciMemStore(id, register_rx_desc_tail(addr), 	rx_desc_tail);
		rx_ring_buff := ring_buffer_build(rx_desc_base_lo, rx_desc_len, rx_desc_head, rx_desc_tail, id, addr);

		// Create a full set of empty descriptors and buffers
		assert rx_desc_base_lo == dev_addr + 512*16 + 512*2*1024;
		assert (512*16 + 512*2*1024) % 4 == 0;
		assert rx_desc_base_lo % 4 == dev_addr % 4;
		build_descriptors(rx_desc_base_lo);

 		// Setup Receiever Control flags
		assert bytes_per_buffer() == 2*1024;	// Make sure we match the 2kb flag below
		PciMemStore(id, register_rx_ctrl(addr), 0x04000100);
	// 				Flags value above corresponds to:
	//				rx_ctrl_broadcast_reject |			  // 0u << 15
	//				//rx_ctrl_broadcast_accept |			  // 1u << 15
	//				rx_ctrl_strip_crc |					  // 1u << 26;
	//				rx_ctrl_loopback_mode_disable |		  // 0u << 6
	//				rx_ctrl_multicast_offset_47_36 |	  // 0
	//				rx_ctrl_buffer_size_2kb |			  // 0x00000000
	//				rx_ctrl_rx_desc_threshold_quarter);   // 1u << 8

		// Setup the rx interrupt delay
		PciMemStore(id, register_rx_delay_timer(addr), 	 rxdelaytimers_rx_delay_timer());
		PciMemStore(id, register_rx_int_abs_timer(addr), rxdelaytimers_rx_absolute_timer());

		// Enable IP and TCP checksum calculation offloading
		PciMemStore(id, register_rx_checksum(addr), 0x00000700);
	// 				Flags value above corresponds to:
	//				rxchecksum_ip_checksum_enable()  |	 // 1u <<  8
	//				rxchecksum_tcp_checksum_enable() |	 // 1u <<  9
	//				rxchecksum_ip6_checksum_enable() )); // 1u << 10

		// Setup Descriptor buffers for tx
		PciMemStore(id, register_tx_desc_base_lo(addr),	tx_desc_base_lo);
		PciMemStore(id, register_tx_desc_base_hi(addr),	0);
		PciMemStore(id, register_tx_desc_length(addr), 	tx_desc_len);
		PciMemStore(id, register_tx_desc_head(addr),	tx_desc_head);
		PciMemStore(id, register_tx_desc_tail(addr), 	tx_desc_tail);
		tx_ring_buff := ring_buffer_build(tx_desc_base_lo, tx_desc_len, tx_desc_head, tx_desc_tail, id, addr);

		// Create a full set of empty descriptors and buffers
		build_descriptors(tx_desc_base_lo);

		// Setup Transmit Control flags
		PciMemStore(id, register_tx_ctrl(addr), 0x000400F8);
	// 				Flags value above corresponds to:
	//				tx_ctrl_pad_short_packets() |		//    1u << 3
	//				tx_ctrl_coll_threshold_default() |	// 0x0fu << 4
	//				tx_ctrl_coll_distance_default());   // 0x40u << 12

		// Setup Transmit Inter Frame Gap
		PciMemStore(id, register_tx_ipg(addr), tx_default_ipg());


		// Start receiving
		temp_reg := PciMemLoad(id, register_rx_ctrl(addr));
		temp_reg := BitwiseOrInstruction(temp_reg, ctrl_rx_enable());
		PciMemStore(id, register_rx_ctrl(addr), temp_reg);


		// Start transmitting
		temp_reg := PciMemLoad(id, register_tx_ctrl(addr));
		temp_reg := BitwiseOrInstruction(temp_reg, ctrl_tx_enable());
		PciMemStore(id, register_tx_ctrl(addr), temp_reg);


		net_init := true;
		b := true;
		assert DeviceMemAddr() == tx_desc_base_lo;
	}
}

// Setup a static set of descriptors pointing at a static set of buffers.
method build_descriptors(addr:int)
	requires addr % 4 == 0;
	requires 512 == num_descriptors();
	requires 16 == bytes_per_descriptor();
	requires 2*1024 == bytes_per_buffer();
	requires word(addr);
	requires word(addr + total_desc_bytes() + total_buffer_bytes());
	requires DeviceMemAddr() <= addr && addr + total_desc_bytes() + total_buffer_bytes() <= DeviceMemAddr() + DeviceMemSize();
{
	var desc_index := 0;

	while (desc_index < 512) 
	{
		var desc_addr := addr + desc_index * 16;
		var buff_addr := addr + total_desc_bytes() + desc_index * 2 * 1024;
		DeviceMemStore(desc_addr + 0, buff_addr, false, 0, []);
		DeviceMemStore(desc_addr + 4, 0, false, 0, []);
		DeviceMemStore(desc_addr + 8, 0, false, 0, []);
		DeviceMemStore(desc_addr +12, 0, false, 0, []);

		desc_index := desc_index + 1;
	}
}

/****************************************
      Ring buffers used for tx/rx
 ****************************************/
datatype ring_buffer = ring_buffer_build(base:int, size:int, head:int, tail:int, id:int, reg_addr:int);

function valid_ring_buffer(rb:ring_buffer):bool
	requires num_descriptors() == 512;
{
	rb.base % 16 == 0 && rb.base >= 0 &&
	word(rb.base + total_desc_bytes() + total_buffer_bytes()) && // Include space for descriptors and the buffers they point at
	DeviceMemAddr() <= rb.base && rb.base + total_desc_bytes() + total_buffer_bytes() < DeviceMemAddr() + DeviceMemSize() &&
	DeviceMemSize() >= 0x204000 &&
	rb.size % 128 == 0 && 128 <= rb.size < power2(19) &&
	rb.size / 16 == 512 && 
	word(rb.base + rb.size) &&
	0 <= rb.head < power2(16) && rb.base + 16*rb.head <= rb.base + rb.size - 16 && // Assuming head and tail are measured in descriptors (16B each)
	0 <= rb.tail < power2(16) && rb.base + 16*rb.tail <= rb.base + rb.size - 16 && // Assuming head and tail are measured in descriptors (16B each)
	rb.reg_addr == PciMemAddr(rb.id) && rb.reg_addr % 4 == 0 && rb.reg_addr >= 0 && word(rb.reg_addr + 128*1024) && 
	IsValidPciId(rb.id) && PciMemSize(rb.id) >= 128*1024
//	0 <= rb.count < num_descriptors() &&
//	rb.head + rb.count % 512 == rb.tail
}

// We expect the input to be: 
// [generic_packet]
//              [app_packet]
// Where the two packets overlap by app_offset bytes, and the total length in bytes is total_len_in_bytes
method {:timeLimit 25} net_tx(tx_buff:ring_buffer, generic_packet:seq<int>, app_packet:seq<int>, 
                              app_offset:int, ignored_bytes:int, total_len_in_bytes:int) 
                              returns (new_tx_buff:ring_buffer)
	requires net_init;
	requires valid_ring_buffer(tx_buff);
	requires is_word_seq(generic_packet);
	requires is_word_seq(app_packet);

  requires 0 <= app_offset < 4;
  requires 0 <= ignored_bytes < 4;
  requires app_offset > 0 ==> |generic_packet| >= 1;
  requires 4 * |generic_packet| + 4 * |app_packet| - app_offset - ignored_bytes == total_len_in_bytes;
  requires 0 < total_len_in_bytes;  // Sorry, not going to send empty packets

  requires |app_packet| <= 375;

  requires total_len_in_bytes <= 2048;  // Ensures the real_packet will fit in a single buffer

  requires left(generic_packet) == right(generic_packet);
  requires app_approves_disclosure(left(app_packet), right(app_packet), 375);

	requires num_descriptors() == 512;
	ensures  valid_ring_buffer(new_tx_buff);
{
	// Write the real_packet data to the buffer indicated by the tail pointer
	var data_buffer := tx_buff.base + total_desc_bytes() + tx_buff.tail*2048; // == bytes_per_buffer
	var addr := data_buffer;
	var i := 0;
	lemma_2toX();

  // Write out the generic portion of the packet
  if (|generic_packet| > 0) {
    ghost var complete := false;
    while (i < |generic_packet|) 
      invariant i < |generic_packet| ==> !complete;
      invariant !complete ==> 0 <= i < |generic_packet|;
      invariant is_word_seq(generic_packet);
      invariant word(addr);
      invariant addr == data_buffer + 4 * i;
      invariant valid_ring_buffer(tx_buff);
      invariant !complete ==> DeviceMemAddr() <= addr && addr < DeviceMemAddr() + DeviceMemSize();
      invariant left(generic_packet) == right(generic_packet);
      invariant app_approves_disclosure(left(app_packet), right(app_packet), 375);
      invariant complete ==> i == |generic_packet|;
    {	
      DeviceMemStore(addr, generic_packet[i], false, i, generic_packet);
      addr := addr + 4;
      i := i + 1;
      if (i == |generic_packet|) {
        complete := true;
      }
    }
  }

  assert addr == data_buffer + 4 * |generic_packet|;

  // Adjust addr to account for overlap between generic_packet and app_packet
  addr := addr - app_offset;

  // Write out the app-specific data
  if (|app_packet| > 0 ) {
    i := 0;
    ghost var completed := false;
    while (i < |app_packet|) 
      invariant i < |app_packet| ==> !completed;
      invariant !completed ==> 0 <= i < |app_packet|;
      invariant is_word_seq(app_packet);
      invariant word(addr);
      invariant !completed ==> addr == data_buffer + 4 * |generic_packet| - app_offset + 4 * i;
      invariant valid_ring_buffer(tx_buff);
      invariant !completed ==> DeviceMemAddr() <= addr && addr < DeviceMemAddr() + DeviceMemSize();
      invariant app_approves_disclosure(left(app_packet), right(app_packet), 375);
    {	
      DeviceMemStore(addr, app_packet[i], true, i, app_packet);
      addr := addr + 4;
      i := i + 1;
      if (i == |app_packet|) {
        completed := true;
      }
    }
  }

	// Update the corresponding descriptor 
	DeviceMemStore(tx_buff.base + 16*tx_buff.tail + 12, 0, false, 0, []);  // Set Special || CSS || RSV || Status to 0
	var temp_reg := 0x09000000;  // (Report Status (RS) (bit 3) || EOP (bit 0) << 24)
	lemma_2toX();
	temp_reg := BitwiseOrInstruction(temp_reg, total_len_in_bytes);
	DeviceMemStore(tx_buff.base + 16*tx_buff.tail + 8, temp_reg, false, 0, []);  // Set CMD || CSO || Length

	// Wait for the next descriptor to reach the done state
	var new_tail := ModInstruction(tx_buff.tail+1, 512);
	assert new_tail == INTERNAL_mod(tx_buff.tail+1, 512);
	lemma_mod_512_forall();
	assert new_tail == (tx_buff.tail+1) % 512;
	assert 0 <= new_tail < 512;
	var done := 0;
	while (done != 1) 
		invariant valid_ring_buffer(tx_buff);
		decreases *;
	{
		var next_desc_status := DeviceMemLoad(tx_buff.base + 16*new_tail + 12);
		done := BitwiseAndInstruction(next_desc_status, 1); // Check bit 0
	}

	// Advance the tail
	DeviceMemStore(tx_buff.base + 16*new_tail + 12, 0, false, 0, []);					// Clear out the status register	
	PciMemStore(tx_buff.id, register_tx_desc_tail(tx_buff.reg_addr), new_tail); // Advance the tail register

	new_tx_buff := ring_buffer_build(tx_buff.base, tx_buff.size, tx_buff.head, new_tail, tx_buff.id, tx_buff.reg_addr);
}

method net_rx(rx_buff:ring_buffer) returns (success:bool, new_rx_buff:ring_buffer, packet:seq<int>, len_in_bytes:int)
	requires net_init;
	requires valid_ring_buffer(rx_buff);
	requires num_descriptors() == 512;
	ensures  valid_ring_buffer(new_rx_buff);
	ensures  success ==> is_word_seq(packet);		// Make sure callers can't use contents if !success
	ensures  success ==> 0 <= len_in_bytes <= 4 * |packet|;
	ensures  success ==> |packet| < power2(16);
{
	success := true;
	var tail:int := rx_buff.tail;
	packet := [];
	len_in_bytes := 0;

	lemma_2toX();
	// Wait for the tail descriptor to be ready
	var found:bool := false;
	while (!found) 
		decreases *;
  		invariant is_word_seq(packet);
		invariant 0 <= tail < power2(16) && rx_buff.base + 16*tail < rx_buff.base + rx_buff.size;
		invariant 0 <= len_in_bytes <= 4 * |packet|;		
		invariant |packet| < power2(16);
	{		
		var special_errs_status := DeviceMemLoad(rx_buff.base + 16*tail + 12);
		var done := BitwiseAndInstruction(special_errs_status, 1); // Bit 0
		if (done == 1) {
			var read_buffer, data, len := read_buffer_data(rx_buff);
			packet := packet + data;		
			len_in_bytes := len_in_bytes + len;

			if (!read_buffer || |packet| >= 0x10000) {
				// Packet is way longer than expected, so start dropping bytes to keep the length reasonable
				success := false;
				packet := [];
				len_in_bytes := 0;
			}

			// Advance both our record of the the tail pointer, and the tail register
			ghost var old_tail := tail;
			tail := ModInstruction(tail+1, 512);
			assert tail == INTERNAL_mod(old_tail+1, 512);
			lemma_mod_512_forall();
			assert tail == (old_tail+1) % 512;
			assert 0 <= tail < 512;
			DeviceMemStore(rx_buff.base + 16*tail + 12, 0, false, 0, []);					// Clear out the status register
			PciMemStore(rx_buff.id, register_rx_desc_tail(rx_buff.reg_addr), tail); // Advance the tail register

			// Did we reach the end of the current packet?
			var eop := BitwiseAndInstruction(special_errs_status, 2); 	 // Bit 1
			if (eop > 0) {
				found := true;
			}			
		}
	}

	new_rx_buff := ring_buffer_build(rx_buff.base, rx_buff.size, rx_buff.head, tail, rx_buff.id, rx_buff.reg_addr);	
}

method read_buffer_data(rx_buff:ring_buffer) returns (success:bool, data:seq<int>, len_in_bytes:int)
	requires valid_ring_buffer(rx_buff);
	ensures  success ==> is_word_seq(data);  // Make sure callers can't use contents if !success
	ensures  success ==> 0 <= len_in_bytes <= 4 * |data|;
	ensures  success ==> 0 <= len_in_bytes <= 2048;
	ensures  success ==> |data| <= 512;
{
	success := true;
	lemma_2toX();
	var len := DeviceMemLoad(rx_buff.base + 16*rx_buff.tail + 8);
	len := BitwiseAndInstruction(len, 0xFFFF);		// Len is lower 16 bits

	if (len > 2048) {	// Packet bizarrely big, given the buffer is only 2K bytes!
		success := false;
	} else {
		// Read in the packet data from its buffer
		data := [];
		var data_buffer := rx_buff.base + total_desc_bytes() + rx_buff.tail*2048; // == bytes_per_buffer
		var addr := data_buffer;
		var num_ints := ((len-1) / 4) + 1;
		assert 0 <= num_ints <= 512;
		var i := 0;
		//assert 0 <= num_ints;	
		while (addr < data_buffer + 4*num_ints) 
  			invariant is_word_seq(data);
			invariant word(addr) && addr % 4 == 0;
			invariant |data| == i;
			invariant addr == data_buffer + 4*i;
			invariant 0 <= i <= 512;
			invariant DeviceMemAddr() <= addr && addr <= DeviceMemAddr() + DeviceMemSize();
		{
			var datum := DeviceMemLoad(addr);
			data := data + [datum];
			addr := addr + 4;
			i := i + 1;
		}

		len_in_bytes := len;
	}
}
