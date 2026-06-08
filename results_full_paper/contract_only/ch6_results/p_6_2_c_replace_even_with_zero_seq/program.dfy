method p_6_2_c_replace_even_with_zero_seq(inputs: seq<int>) returns (result: seq<int>)
	ensures |result| == |inputs|
	ensures forall i :: 0 <= i < |inputs| ==> (inputs[i] % 2 == 0 ==> result[i] == 0) && (inputs[i] % 2 != 0 ==> result[i] == inputs[i])
{
  result := seq(|inputs|, i requires 0 <= i < |inputs| => if inputs[i] % 2 == 0 then 0 else inputs[i]);
}