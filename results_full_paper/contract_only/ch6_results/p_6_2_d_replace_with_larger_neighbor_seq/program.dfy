method p_6_2_d_replace_with_larger_neighbor_seq(inputs: seq<int>) returns (result: seq<int>)
	requires |inputs| >= 3
	ensures |result| == |inputs|
	ensures result[0] == inputs[0]
	ensures result[|inputs| - 1] == inputs[|inputs| - 1]
	ensures forall i :: 1 <= i < |inputs| - 1 ==> result[i] == if inputs[i - 1] >= inputs[i + 1] then inputs[i - 1] else inputs[i + 1]
{
  var n := |inputs|;
  result := [inputs[0]];
  var i := 1;
  while i < n - 1
    invariant n == |inputs|
    invariant 1 <= i <= n - 1
    invariant |result| == i
    invariant result[0] == inputs[0]
    invariant forall j :: 1 <= j < i ==> result[j] == if inputs[j - 1] >= inputs[j + 1] then inputs[j - 1] else inputs[j + 1]
    decreases n - 1 - i
  {
    var v := if inputs[i - 1] >= inputs[i + 1] then inputs[i - 1] else inputs[i + 1];
    result := result + [v];
    i := i + 1;
  }
  result := result + [inputs[n - 1]];
}