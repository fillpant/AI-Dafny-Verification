method p_4_2_a_min_max_seq(inputs: seq<int>) returns (min: int, max: int)
	requires 0 < |inputs|
	ensures forall i :: 0 <= i < |inputs| ==> min <= inputs[i]
	ensures forall i :: 0 <= i < |inputs| ==> max >= inputs[i]
	ensures exists i :: 0 <= i < |inputs| && min == inputs[i]
	ensures exists i :: 0 <= i < |inputs| && max == inputs[i]
{
  min := inputs[0];
  max := inputs[0];
  ghost var minIdx := 0;
  ghost var maxIdx := 0;
  var j := 1;

  while j < |inputs|
    invariant 1 <= j <= |inputs|
    invariant 0 <= minIdx < j
    invariant 0 <= maxIdx < j
    invariant min == inputs[minIdx]
    invariant max == inputs[maxIdx]
    invariant forall i :: 0 <= i < j ==> min <= inputs[i]
    invariant forall i :: 0 <= i < j ==> max >= inputs[i]
    decreases |inputs| - j
  {
    if inputs[j] < min {
      min := inputs[j];
      minIdx := j;
    }

    if inputs[j] > max {
      max := inputs[j];
      maxIdx := j;
    }

    j := j + 1;
  }
}