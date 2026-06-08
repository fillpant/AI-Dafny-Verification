method p_4_6_find_minimum_seq(inputs: seq<int>) returns (min: int)
	requires 0 < |inputs|
	ensures forall i :: 0 <= i < |inputs| ==> min <= inputs[i]
	ensures exists i :: 0 <= i < |inputs| && min == inputs[i]
{
  var idx := 1;
  var minIndex := 0;
  min := inputs[0];

  while idx < |inputs|
    invariant 1 <= idx <= |inputs|
    invariant 0 <= minIndex < idx
    invariant min == inputs[minIndex]
    invariant forall i :: 0 <= i < idx ==> min <= inputs[i]
  {
    if inputs[idx] < min {
      min := inputs[idx];
      minIndex := idx;
    }
    idx := idx + 1;
  }
}