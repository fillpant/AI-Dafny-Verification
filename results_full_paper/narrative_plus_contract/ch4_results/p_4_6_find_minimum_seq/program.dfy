method p_4_6_find_minimum_seq(inputs: seq<int>) returns (min: int)
	requires 0 < |inputs|
	ensures forall i :: 0 <= i < |inputs| ==> min <= inputs[i]
	ensures exists i :: 0 <= i < |inputs| && min == inputs[i]
{
  min := inputs[0];
  var i := 1;
  var k := 0;

  while i < |inputs|
    invariant 1 <= i <= |inputs|
    invariant 0 <= k < i
    invariant min == inputs[k]
    invariant forall j :: 0 <= j < i ==> min <= inputs[j]
  {
    if inputs[i] < min {
      min := inputs[i];
      k := i;
    }
    i := i + 1;
  }

  assert 0 <= k < |inputs| && min == inputs[k];
  assert exists j :: 0 <= j < |inputs| && min == inputs[j];
}