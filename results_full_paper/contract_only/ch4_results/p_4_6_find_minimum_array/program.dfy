method p_4_6_find_minimum_array(inputs: array<int>) returns (min: int)
	requires 0 < inputs.Length
	ensures forall i :: 0 <= i < inputs.Length ==> min <= inputs[i]
	ensures exists i :: 0 <= i < inputs.Length && min == inputs[i]
{
  min := inputs[0];
  var idx := 1;
  while idx < inputs.Length
    invariant 1 <= idx <= inputs.Length
    invariant forall i :: 0 <= i < idx ==> min <= inputs[i]
    invariant exists i :: 0 <= i < idx && min == inputs[i]
  {
    if inputs[idx] < min {
      min := inputs[idx];
    }
    idx := idx + 1;
  }
}