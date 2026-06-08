method p_6_2_a_swap_first_last_seq(inputs: seq<int>) returns (result: seq<int>)
	requires |inputs| >= 2
	ensures |result| == |inputs|
	ensures result[0] == inputs[|inputs| - 1]
	ensures result[|inputs| - 1] == inputs[0]
	ensures forall i :: 1 <= i < |inputs| - 1 ==> result[i] == inputs[i]
{
  result := inputs[0 := inputs[|inputs| - 1]][|inputs| - 1 := inputs[0]];
}