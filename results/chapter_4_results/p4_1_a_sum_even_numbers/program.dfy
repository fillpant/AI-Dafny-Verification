method p4_1_a_sum_even_numbers() returns (sum: int)
	ensures sum == 2550
{
  var i := 2;
  sum := 0;
  while i <= 100
    invariant i % 2 == 0
    invariant 2 <= i <= 102
    invariant sum == ((i - 2) / 2) * (((i - 2) / 2) + 1)
  {
    sum := sum + i;
    i := i + 2;
  }
}