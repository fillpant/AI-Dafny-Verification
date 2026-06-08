method p_6_1_d_process_array_first_and_last_seq(inputs: seq<int>) returns (first_and_last: seq<int>)
	requires |inputs| == 10
	ensures first_and_last == [inputs[0], inputs[|inputs| - 1]]
{
  first_and_last := [inputs[0], inputs[|inputs| - 1]];
}