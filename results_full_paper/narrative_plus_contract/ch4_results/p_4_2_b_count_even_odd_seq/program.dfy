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

method p_4_2_b_count_even_odd_seq(inputs: seq<int>) returns (even_count: int, odd_count: int)
	ensures even_count == number_even(inputs)
	ensures odd_count == number_odd(inputs)
{
  if inputs == [] {
    even_count := 0;
    odd_count := 0;
  } else {
    var e, o := p_4_2_b_count_even_odd_seq(inputs[1..]);
    if inputs[0] % 2 == 0 {
      even_count := e + 1;
      odd_count := o;
    } else {
      even_count := e;
      odd_count := o + 1;
    }
  }
}