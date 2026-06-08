function factorial(n : int) : int
  decreases n
{
  if n <= 1 then 1 else n * factorial(n - 1)
}

method p_1_3() returns (i : int)
	ensures i == factorial(10)
{
  i := 1 * 2 * 3 * 4 * 5 * 6 * 7 * 8 * 9 * 10;
}