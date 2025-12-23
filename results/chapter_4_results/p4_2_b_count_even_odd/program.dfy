function number_odd(s:seq<int>): int
{ if s == [] then 0
  else if s[0] % 2 == 1 then 1 + number_odd(s[1..])
  else number_odd(s[1..])
}

function number_even (s:seq<int>): int
{ if s == [] then 0
  else if s[0] % 2 == 0 then 1 + number_even(s[1..])
  else number_even(s[1..])
}

method p4_2_b_count_even_odd(inputs: seq<int>) returns (even_count: int, odd_count: int)
	ensures even_count == number_even(inputs[..])
	ensures odd_count == number_odd(inputs[..])
{
  var i := 0;
  even_count := 0;
  odd_count := 0;
  while i < |inputs|
    invariant 0 <= i <= |inputs|
    invariant even_count == number_even(inputs[..i])
    invariant odd_count == number_odd(inputs[..i])
    decreases |inputs| - i
  {
    // First advance i so the slice inputs[..i] includes the next element
    i := i + 1;

    if inputs[i-1] % 2 == 0 {
      even_count := even_count + 1;
    } else {
      odd_count := odd_count + 1;
    }
  }
}