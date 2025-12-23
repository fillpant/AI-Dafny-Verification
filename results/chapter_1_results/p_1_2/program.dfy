method p_1_2() returns (i : int)
	ensures i == (10 * 11) / 2
{
  var sum := 0;
  var k := 1;
  while k <= 10
    invariant 1 <= k && k <= 11
    invariant sum == (k - 1) * k / 2
  {
    sum := sum + k;
    k := k + 1;
  }
  i := sum;
}