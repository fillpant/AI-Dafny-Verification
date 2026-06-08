method p4_6_find_minimum(inputs: array<int>) returns (min: int)
	requires 0 < inputs.Length
	ensures forall i :: 0 <= i < inputs.Length ==> min <= inputs[i]
	ensures exists i :: 0 <= i < inputs.Length && min == inputs[i]
{
  var minIndex := 0;
  min := inputs[0];
  var i := 1;
  while i < inputs.Length
    invariant 1 <= i <= inputs.Length
    invariant 0 <= minIndex < i
    invariant min == inputs[minIndex]
    invariant forall j :: 0 <= j < i ==> min <= inputs[j]
  {
    if inputs[i] < min {
      min := inputs[i];
      minIndex := i;
    }
    i := i + 1;
  }
}