/* Ethernet-level interface to the network */

include "../../Drivers/Network/Intel/Device.dfy"
include "../Util/arrays_and_seqs.dfy"

//method mac_addr_to_bytes(hi:int, lo:int) returns (addr:seq<int>)
//	requires 0 <= hi < power2(16);
//	requires word(lo);
//	ensures byte_seq(addr, 6); 
//{
//	lemma_2toX();
//	var hi_bytes := word_2_bytes(hi);
//	var lo_bytes := word_2_bytes(lo);
//	addr := hi_bytes[2..] + lo_bytes;	// Cut the two zeroes at the top
//}

// TODO: Require the app is okay to expose this data!
method tx_ethernet(tx_buff:ring_buffer, dst:ethernet_addr, data:seq<int>, num_ignored_bytes:int) 
  returns (new_tx_buff:ring_buffer)
	requires net_init;
	requires valid_ring_buffer(tx_buff);
	requires valid_ethernet_addr(dst);
	requires is_word_seq(data);
	requires 12 <= |data| <= 375;
  requires 0 <= num_ignored_bytes < 4;
  requires |data| == 12 ==> num_ignored_bytes <= 2; // Need 46 bytes total
  requires app_approves_disclosure(left(data), right(data), 375); 
	ensures  valid_ring_buffer(new_tx_buff);
{
	lemma_2toX();
	var src_addr := my_ethernet_addr();
	
	var type_bytes := [ 0x08, 0x00];	// Fix the type to be IP
	var header := dst.bytes + src_addr.bytes + type_bytes;

  assert app_approves_disclosure(left(data), right(data), 375); 
  var header_words := byte_seq_to_word_seq(header);
  assert data == old(data);

  assert left(header_words) == right(header_words);
  assert app_approves_disclosure(left(data), right(data), 375); 
	new_tx_buff := net_tx(tx_buff, header_words, data, 2, num_ignored_bytes, 14+|data|*4-num_ignored_bytes);
}

// TODO: Check endian-ness of everything!

method rx_ethernet(rx_buff:ring_buffer) returns (success:bool, new_rx_buff:ring_buffer, src:ethernet_addr, data:seq<int>)
	requires net_init;
	requires valid_ring_buffer(rx_buff);
	ensures success ==> valid_ethernet_addr(src);
	ensures success ==> is_byte_seq(data);
	ensures success ==> 50 <= |data| <= 1500;
	ensures valid_ring_buffer(new_rx_buff);
{
	lemma_2toX();
	var len_in_bytes:int, data_words:seq<int>;
	success, new_rx_buff, data_words, len_in_bytes := net_rx(rx_buff);

	if (success) {
		var data_bytes := word_seq_to_byte_seq(data_words);
		assert is_byte_seq(data_bytes);
		assert |data_bytes| == 4 * |data_words|;


		if (len_in_bytes < 64) {	// Too short for an Ethernet packet
			success := false;		
		} else {
			var dst_bytes:seq<int> := data_bytes[0..6];
			var src_bytes:seq<int> := data_bytes[6..12];
			assert(|dst_bytes| == 6 && |src_bytes| == 6);	
			assert is_byte_seq(src_bytes);	
			src := ethernet_addr_builder(src_bytes);
			assert valid_ethernet_addr(src);

			// Is it for us?
			var i := 0;
			while (i < 6) 
				invariant 0 <= i <= 6;
				invariant forall j :: 0 <= j < i ==> success ==> dst_bytes[j] == my_ethernet_addr().bytes[j];
				invariant is_byte_seq(data_bytes);
				invariant |data_bytes| >= 64;
				invariant valid_ethernet_addr(src);					
			{
				if (dst_bytes[i] != my_ethernet_addr().bytes[i]) {
					success := false;
				}
				i := i + 1;
			}

			// TODO: Do we need to read these, or is the returned len_in_bytes sufficient?
			var type_bytes := data_bytes[12..14];
			assert |type_bytes| == 2;

			if (type_bytes[0] != 0x08 || type_bytes[1] != 0x00) { // Insist on IP
				success := false;
			}

			// Remove the header, and cut down to 1500 if we happened to get more than expected
			var len := len_in_bytes-14;
			if (len > 1500) {
				len := 1500;
			}
      
			
			var body := data_bytes[14..|data_bytes|];
			lemma_byte_seq_sub_seq(data_bytes, body, 14, |data_bytes|);

			data := body[0..len];
			lemma_byte_seq_sub_seq(body, data, 0, len);
		}
	}
}
