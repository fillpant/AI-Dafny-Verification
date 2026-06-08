function sum_array(inputs: seq<int>, i: int): int
{
  if |inputs| == 0 then 0
  else inputs[0] * i + sum_array(inputs[1..], i * -1)
}

method p_6_6_alternating_sum_seq(inputs: seq<int>) returns (alt_sum: int)
	ensures alt_sum == sum_array(inputs, 1)
{
  if |inputs| == 0 {
    alt_sum := 0;
  } else if |inputs| == 1 {
    assert inputs[1..] == [];
    alt_sum := inputs[0];
  } else {
    assert 2 <= |inputs|;
    assert 0 < |inputs[1..]|;
    assert (inputs[1..])[0] == inputs[1];
    assert (inputs[1..])[1..] == inputs[2..];
    var rest := p_6_6_alternating_sum_seq(inputs[2..]);
    alt_sum := inputs[0] - inputs[1] + rest;
  }
}