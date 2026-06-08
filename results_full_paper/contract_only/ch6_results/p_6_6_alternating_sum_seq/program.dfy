function sum_array(inputs: seq<int>, i: int): int
{
  if |inputs| == 0 then 0
  else inputs[0] * i + sum_array(inputs[1..], i * -1)
}

method p_6_6_alternating_sum_seq(inputs: seq<int>) returns (alt_sum: int)
	ensures alt_sum == sum_array(inputs, 1)
{
  alt_sum := 0;
  var idx := 0;
  var sgn := 1;

  assert inputs[0..] == inputs;
  while idx < |inputs|
    invariant 0 <= idx <= |inputs|
    invariant alt_sum + sum_array(inputs[idx..], sgn) == sum_array(inputs, 1)
    decreases |inputs| - idx
  {
    var oldIdx := idx;
    var oldSgn := sgn;
    var oldAlt := alt_sum;

    assert oldIdx < |inputs|;
    assert |inputs[oldIdx..]| > 0;
    assert (inputs[oldIdx..])[0] == inputs[oldIdx];
    assert (inputs[oldIdx..])[1..] == inputs[oldIdx + 1..];
    assert sum_array(inputs[oldIdx..], oldSgn) == inputs[oldIdx] * oldSgn + sum_array(inputs[oldIdx + 1..], oldSgn * -1);

    alt_sum := oldAlt + inputs[oldIdx] * oldSgn;
    sgn := oldSgn * -1;
    idx := oldIdx + 1;

    assert alt_sum + sum_array(inputs[idx..], sgn) == sum_array(inputs, 1);
  }

  assert idx == |inputs|;
  assert inputs[idx..] == [];
  assert sum_array(inputs[idx..], sgn) == 0;
  assert alt_sum == sum_array(inputs, 1);
}