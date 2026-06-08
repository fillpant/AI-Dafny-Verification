method p_4_1_a_sum_even_numbers() returns (sum: int)
	ensures sum == 2550
{
  sum := 0;
  var n := 1;
  while n <= 50
    invariant 1 <= n <= 51
    invariant sum == n * (n - 1)
    decreases 51 - n
  {
    sum := sum + 2 * n;
    n := n + 1;
  }
  assert n == 51;
  assert sum == 51 * 50;
  assert sum == 2550;
}