function sum_array(inputs: seq<int>): int
  ensures sum_array(inputs) == (if |inputs| == 0 then 0 else inputs[0] + sum_array(inputs[1..]))
{
  if |inputs| == 0 then 0
  else inputs[0] + sum_array(inputs[1..])
}

method p_13_9_recursive_sum_array(inputs: array<int>) returns (sum: int)
	ensures sum == sum_array(inputs[..])
{
  sum := 0;
  var i := inputs.Length;
  while i > 0
    invariant 0 <= i <= inputs.Length
    invariant sum == sum_array(inputs[i..])
    decreases i
  {
    var oldI := i;
    i := i - 1;
    assert oldI == i + 1;
    assert sum == sum_array(inputs[oldI..]);
    assert sum == sum_array(inputs[i + 1..]);
    assert inputs[i..] == [inputs[i]] + inputs[i + 1..];
    assert inputs[i..][0] == inputs[i];
    assert inputs[i..][1..] == inputs[i + 1..];
    assert sum_array(inputs[i..]) == inputs[i] + sum_array(inputs[i + 1..]);
    sum := inputs[i] + sum;
    assert sum == sum_array(inputs[i..]);
  }
  assert i == 0;
  assert inputs[i..] == inputs[..];
}