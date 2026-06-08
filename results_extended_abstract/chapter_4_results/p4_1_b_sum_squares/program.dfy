method p4_1_b_sum_squares() returns (sum: int)
	ensures sum == 338350
{
  var i := 1;
  sum := 0;
  while i <= 100
    invariant 1 <= i <= 101
    invariant sum == (i - 1) * i * (2 * (i - 1) + 1) / 6
  {
    sum := sum + i * i;
    i := i + 1;
  }
}