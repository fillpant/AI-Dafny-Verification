function sum_array(inputs: seq<int>, i: int): int
{
  if |inputs| == 0 then 0
  else inputs[0] * i + sum_array(inputs[1..], i * -1)
}

method p_6_6_alternating_sum_array(inputs: array<int>) returns (alt_sum: int)
	ensures alt_sum == sum_array(inputs[..], 1)
{
  alt_sum := 0;
  var idx := 0;
  var sign := 1;

  assert inputs[0..] == inputs[..];
  assert alt_sum + sum_array(inputs[idx..], sign) == sum_array(inputs[..], 1);

  while idx < inputs.Length
    invariant 0 <= idx <= inputs.Length
    invariant alt_sum + sum_array(inputs[idx..], sign) == sum_array(inputs[..], 1)
    decreases inputs.Length - idx
  {
    var oldIdx := idx;
    var oldSign := sign;
    var rest := inputs[oldIdx..];

    assert 0 <= oldIdx < inputs.Length;
    assert |rest| > 0;
    assert rest[0] == inputs[oldIdx];
    assert rest[1..] == inputs[oldIdx + 1..];
    assert sum_array(rest, oldSign) == rest[0] * oldSign + sum_array(rest[1..], oldSign * -1);
    assert sum_array(inputs[oldIdx..], oldSign) == inputs[oldIdx] * oldSign + sum_array(inputs[oldIdx + 1..], oldSign * -1);

    alt_sum := alt_sum + inputs[oldIdx] * oldSign;
    sign := oldSign * -1;
    idx := oldIdx + 1;

    assert alt_sum + sum_array(inputs[idx..], sign) == sum_array(inputs[..], 1);
  }

  assert idx == inputs.Length;
  assert inputs[idx..] == [];
  assert sum_array(inputs[idx..], sign) == 0;
  assert alt_sum == sum_array(inputs[..], 1);
}