method p_6_2_b_shift_right_seq(inputs: seq<int>) returns (result: seq<int>)
	requires |inputs| >= 1
	ensures |result| == |inputs|
	ensures result[0] == inputs[|inputs| - 1]
	ensures forall i :: 1 <= i < |inputs| ==> result[i] == inputs[i - 1]
{
  var n := |inputs|;
  result := [inputs[n - 1]] + inputs[..n - 1];
}