function digits (n:nat): nat
{
    if 0 <= n <= 9 then 1
    else 1 + digits (n/10)
}

method P_3_3_NumberOfDigits (i:int) returns (n: nat)
	requires 10000000000 > i > -10000000000
	ensures i >= 0 ==> n == digits(i)
	ensures i < 0 ==> n == digits(-i)
{
  var j:nat := if i < 0 then -i else i;
  var k:nat := j;
  n := 0;

  if k == 0 {
    n := 1;
    return;
  }

  while k > 0
    invariant k > 0 ==> digits(k) + n == digits(j)
    invariant k == 0 ==> n == digits(j)
    invariant n >= 0
    invariant k <= j
  {
    n := n + 1;
    k := k / 10;
  }
}