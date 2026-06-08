function sum_array(inputs: seq<int>, i: int): int
{
  if |inputs| == 0 then 0
  else inputs[0] * i + sum_array(inputs[1..], i * -1)
}

method p_6_6_alternating_sum_array(inputs: array<int>) returns (alt_sum: int)
	ensures alt_sum == sum_array(inputs[..], 1)
{
  ghost var a := inputs[..];
  alt_sum := 0;
  var i := 0;
  var sign := 1;
  assert a[0..] == a;
  while i < inputs.Length
    invariant 0 <= i <= inputs.Length
    invariant |a| == inputs.Length
    invariant a == inputs[..]
    invariant alt_sum + sum_array(a[i..], sign) == sum_array(a, 1)
    decreases inputs.Length - i
  {
    var oldI := i;
    var oldSign := sign;
    var oldAlt := alt_sum;
    var x := inputs[oldI];

    assert x == a[oldI];
    assert |a[oldI..]| > 0;
    assert (a[oldI..])[0] == a[oldI];
    assert (a[oldI..])[1..] == a[oldI + 1..];
    assert sum_array(a[oldI..], oldSign) == x * oldSign + sum_array(a[oldI + 1..], oldSign * -1);
    assert oldAlt + x * oldSign + sum_array(a[oldI + 1..], oldSign * -1) == sum_array(a, 1);

    alt_sum := oldAlt + x * oldSign;
    sign := oldSign * -1;
    i := oldI + 1;

    assert alt_sum + sum_array(a[i..], sign) == sum_array(a, 1);
  }
  assert i == inputs.Length;
  assert i == |a|;
  assert a[i..] == [];
  assert sum_array(a[i..], sign) == 0;
  assert alt_sum == sum_array(a, 1);
  assert a == inputs[..];
  assert sum_array(a, 1) == sum_array(inputs[..], 1);
}