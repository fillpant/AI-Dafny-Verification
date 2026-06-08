function s_o_d(a: int): int
requires a >= 0
{
  if a == 0 then 0
  else if a % 2 == 0 then s_o_d(a / 10)
  else a % 10 + s_o_d(a / 10)
}

method p4_1_e_sum_odd_digits(a: int) returns (sum: int)
	requires a >= 0
	ensures sum >= 0
	ensures sum == s_o_d(a)
{
  var x := a;
  sum := 0;
  while x > 0
    invariant x >= 0
    invariant sum >= 0
    invariant sum + s_o_d(x) == s_o_d(a)
  {
    var d := x % 10;
    if d % 2 != 0 {
      sum := sum + d;
    }
    x := x / 10;
  }
}