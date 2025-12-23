method p4_2_a_min_max(inputs: array<int>) returns (min: int, max: int)
	requires 0 < inputs.Length
	ensures forall i :: 0 <= i < inputs.Length ==> min <= inputs[i]
	ensures forall i :: 0 <= i < inputs.Length ==> max >= inputs[i]
	ensures exists i :: 0 <= i < inputs.Length && min == inputs[i]
	ensures exists i :: 0 <= i < inputs.Length && max == inputs[i]
{
  var i := 0;
  min := inputs[i];
  max := inputs[i];
  i := i + 1;
  while i < inputs.Length
    invariant 1 <= i <= inputs.Length
    invariant forall j :: 0 <= j < i ==> min <= inputs[j]
    invariant forall j :: 0 <= j < i ==> max >= inputs[j]
    invariant exists j :: 0 <= j < i && min == inputs[j]
    invariant exists j :: 0 <= j < i && max == inputs[j]
  {
    if inputs[i] < min {
      min := inputs[i];
    }
    if inputs[i] > max {
      max := inputs[i];
    }
    i := i + 1;
  }
}