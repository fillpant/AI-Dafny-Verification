method p_4_2_a_min_max_array(inputs: array<int>) returns (min: int, max: int)
	requires 0 < inputs.Length
	ensures forall i :: 0 <= i < inputs.Length ==> min <= inputs[i]
	ensures forall i :: 0 <= i < inputs.Length ==> max >= inputs[i]
	ensures exists i :: 0 <= i < inputs.Length && min == inputs[i]
	ensures exists i :: 0 <= i < inputs.Length && max == inputs[i]
{
  min := inputs[0];
  max := inputs[0];
  var idxMin := 0;
  var idxMax := 0;
  var i := 1;
  while i < inputs.Length
    invariant 1 <= i <= inputs.Length
    invariant 0 <= idxMin < i
    invariant 0 <= idxMax < i
    invariant min == inputs[idxMin]
    invariant max == inputs[idxMax]
    invariant forall j :: 0 <= j < i ==> min <= inputs[j]
    invariant forall j :: 0 <= j < i ==> max >= inputs[j]
  {
    if inputs[i] < min {
      min := inputs[i];
      idxMin := i;
    }
    if inputs[i] > max {
      max := inputs[i];
      idxMax := i;
    }
    i := i + 1;
  }
}