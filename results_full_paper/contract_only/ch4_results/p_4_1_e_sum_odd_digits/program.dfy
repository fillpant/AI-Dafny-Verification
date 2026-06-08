function s_o_d(a: int): int
requires a >= 0
{
  if a == 0 then 0
  else if a % 2 == 0 then s_o_d(a / 10)
  else a % 10 + s_o_d(a / 10)
}

method p_4_1_e_sum_odd_digits(a: int) returns (sum: int)
	requires a >= 0
	ensures sum >= 0
	ensures sum == s_o_d(a)
{
  if a == 0 {
    sum := 0;
  } else if a % 2 == 0 {
    sum := p_4_1_e_sum_odd_digits(a / 10);
  } else {
    var rest := p_4_1_e_sum_odd_digits(a / 10);
    sum := a % 10 + rest;
  }
}