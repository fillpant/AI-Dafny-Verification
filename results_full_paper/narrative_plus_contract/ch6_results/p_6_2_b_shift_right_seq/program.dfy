method p_6_2_b_shift_right_seq(inputs: seq<int>) returns (result: seq<int>)
	requires |inputs| >= 1
	ensures |result| == |inputs|
	ensures result[0] == inputs[|inputs| - 1]
	ensures forall i :: 1 <= i < |inputs| ==> result[i] == inputs[i - 1]
{
  result := seq(|inputs|, i requires 0 <= i < |inputs| =>
    if i == 0 then inputs[|inputs| - 1] else inputs[i - 1]);
}