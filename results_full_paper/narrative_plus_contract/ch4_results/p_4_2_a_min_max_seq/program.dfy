method p_4_2_a_min_max_seq(inputs: seq<int>) returns (min: int, max: int)
	requires 0 < |inputs|
	ensures forall i :: 0 <= i < |inputs| ==> min <= inputs[i]
	ensures forall i :: 0 <= i < |inputs| ==> max >= inputs[i]
	ensures exists i :: 0 <= i < |inputs| && min == inputs[i]
	ensures exists i :: 0 <= i < |inputs| && max == inputs[i]
{
  min := inputs[0];
  max := inputs[0];

  ghost var minIndex := 0;
  ghost var maxIndex := 0;
  var i := 1;

  while i < |inputs|
    invariant 1 <= i <= |inputs|
    invariant 0 <= minIndex < i
    invariant 0 <= maxIndex < i
    invariant min == inputs[minIndex]
    invariant max == inputs[maxIndex]
    invariant forall j :: 0 <= j < i ==> min <= inputs[j]
    invariant forall j :: 0 <= j < i ==> max >= inputs[j]
    decreases |inputs| - i
  {
    if inputs[i] < min {
      min := inputs[i];
      minIndex := i;
    }

    if inputs[i] > max {
      max := inputs[i];
      maxIndex := i;
    }

    i := i + 1;
  }
}