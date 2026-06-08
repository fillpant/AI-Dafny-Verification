method p_6_2_d_replace_with_larger_neighbor_seq(inputs: seq<int>) returns (result: seq<int>)
	requires |inputs| >= 3
	ensures |result| == |inputs|
	ensures result[0] == inputs[0]
	ensures result[|inputs| - 1] == inputs[|inputs| - 1]
	ensures forall i :: 1 <= i < |inputs| - 1 ==> result[i] == if inputs[i - 1] >= inputs[i + 1] then inputs[i - 1] else inputs[i + 1]
{
  result := seq(|inputs|, i =>
    if i == 0 then inputs[0]
    else if i == |inputs| - 1 then inputs[|inputs| - 1]
    else if 1 <= i < |inputs| - 1 then
      if inputs[i - 1] >= inputs[i + 1] then inputs[i - 1] else inputs[i + 1]
    else inputs[0]);
}