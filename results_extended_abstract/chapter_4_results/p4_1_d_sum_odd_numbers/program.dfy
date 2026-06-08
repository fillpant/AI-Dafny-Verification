function sum_odd(a: int, b: int): int
decreases b - a
{
  if a > b then 0
  else if a % 2 == 1 then a + sum_odd(a + 1, b)
  else sum_odd(a + 1, b)
}

method p4_1_d_sum_odd_numbers(a: int, b: int) returns (sum: int)
	ensures sum == sum_odd(a, b)
{
  if a > b {
    sum := 0;
  } else {
    var i := a;
    sum := 0;
    while i < b + 1
      invariant i >= a
      invariant i <= b
      invariant sum == sum_odd(a, i - 1)
      decreases b + 1 - i
    {
      if i % 2 == 1 {
        sum := sum + i;
      }
      i := i + 1;
    }
  }
}