function factorial(n: int): int
  decreases n
{
  if n <= 1 then 1 else n * factorial(n - 1)
}

method p_1_3_product() returns (i: int)
	ensures i == factorial(10)
{
  i := 3628800;
}