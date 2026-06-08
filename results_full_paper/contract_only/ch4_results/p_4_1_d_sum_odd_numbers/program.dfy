function sum_odd(a: int, b: int): int
decreases b - a
{
  if a > b then 0
  else if a % 2 == 1 then a + sum_odd(a + 1, b)
  else sum_odd(a + 1, b)
}

method p_4_1_d_sum_odd_numbers(a: int, b: int) returns (sum: int)
	ensures sum == sum_odd(a, b)
{
  if a > b {
    sum := 0;
    assert sum_odd(a, b) == 0;
  } else {
    sum := 0;
    var i := a;
    while i <= b
      invariant a <= i <= b + 1
      invariant sum + sum_odd(i, b) == sum_odd(a, b)
      decreases b - i + 1
    {
      if i % 2 == 1 {
        assert sum_odd(i, b) == i + sum_odd(i + 1, b);
        sum := sum + i;
      } else {
        assert sum_odd(i, b) == sum_odd(i + 1, b);
      }
      assert sum + sum_odd(i + 1, b) == sum_odd(a, b);
      i := i + 1;
    }
    assert i == b + 1;
    assert sum_odd(i, b) == 0;
    assert sum == sum_odd(a, b);
  }
}