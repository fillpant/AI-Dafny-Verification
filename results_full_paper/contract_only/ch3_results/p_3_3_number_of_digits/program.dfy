function digits (n: nat): nat
{
    if 0 <= n <= 9 then 1
    else 1 + digits (n / 10)
}

method p_3_3_number_of_digits (i: int) returns (n: nat)
	requires 10000000000 > i > -10000000000
	ensures i >= 0 ==> n == digits(i)
	ensures i < 0 ==> n == digits(-i)
{
  var x: nat;
  if i < 0 {
    assert -i > 0;
    x := -i;
  } else {
    assert i >= 0;
    x := i;
  }

  var y: nat := x;
  n := 1;
  while y >= 10
    invariant n + digits(y) == 1 + digits(x)
    decreases y
  {
    var z: nat := y / 10;
    assert z < y;
    assert !(0 <= y <= 9);
    assert digits(y) == 1 + digits(z);
    calc {
      (n + 1) + digits(z);
      ==
      n + (1 + digits(z));
      ==
      n + digits(y);
      ==
      1 + digits(x);
    }
    n := n + 1;
    y := z;
  }

  assert 0 <= y <= 9;
  assert digits(y) == 1;
  assert n + digits(y) == 1 + digits(x);
  assert n + 1 == 1 + digits(x);
  assert 1 + digits(x) == digits(x) + 1;
  assert n + 1 == digits(x) + 1;
  assert n == digits(x);

  if i >= 0 {
    assert x == i;
    assert n == digits(i);
  } else {
    assert x == -i;
    assert n == digits(-i);
  }
}