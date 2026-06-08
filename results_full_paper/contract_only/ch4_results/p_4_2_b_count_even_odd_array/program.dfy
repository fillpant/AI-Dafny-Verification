function number_odd(s: seq<int>): int
{ if s == [] then 0
  else if s[0] % 2 == 1 then 1 + number_odd(s[1..])
  else number_odd(s[1..])
}

function number_even (s: seq<int>): int
{ if s == [] then 0
  else if s[0] % 2 == 0 then 1 + number_even(s[1..])
  else number_even(s[1..])
}

method p_4_2_b_count_even_odd_array(inputs: array<int>) returns (even_count: int, odd_count: int)
	ensures even_count == number_even(inputs[..])
	ensures odd_count == number_odd(inputs[..])
{
  even_count := 0;
  odd_count := 0;
  var i := inputs.Length;

  while i > 0
    invariant 0 <= i <= inputs.Length
    invariant even_count == number_even(inputs[i..])
    invariant odd_count == number_odd(inputs[i..])
    decreases i
  {
    i := i - 1;
    assert 0 <= i < inputs.Length;
    assert even_count == number_even(inputs[i + 1..]);
    assert odd_count == number_odd(inputs[i + 1..]);
    assert inputs[i..][0] == inputs[i];
    assert inputs[i..][1..] == inputs[i + 1..];

    if inputs[i] % 2 == 0 {
      assert number_even(inputs[i..]) == 1 + number_even(inputs[i + 1..]);
      assert number_odd(inputs[i..]) == number_odd(inputs[i + 1..]);
      even_count := even_count + 1;
    } else {
      assert 0 <= inputs[i] % 2 < 2;
      assert inputs[i] % 2 == 1;
      assert number_even(inputs[i..]) == number_even(inputs[i + 1..]);
      assert number_odd(inputs[i..]) == 1 + number_odd(inputs[i + 1..]);
      odd_count := odd_count + 1;
    }
  }

  assert i == 0;
  assert inputs[i..] == inputs[..];
}