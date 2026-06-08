method p_6_1_a_process_array_even_indexed_seq(inputs: seq<int>) returns (even_indexed: seq<int>)
	requires |inputs| == 10
	ensures even_indexed == [inputs[0], inputs[2], inputs[4], inputs[6], inputs[8]]
{
  even_indexed := [inputs[0], inputs[2], inputs[4], inputs[6], inputs[8]];
}