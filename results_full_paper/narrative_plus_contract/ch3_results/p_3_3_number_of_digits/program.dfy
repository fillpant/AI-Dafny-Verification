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
  var x: int;
  if i < 0 {
    x := -i;
  } else {
    x := i;
  }

  assert 0 <= x;
  assert x < 10000000000;
  var y: nat := x;

  var a0: nat := y;
  var a1: nat := a0 / 10;
  var a2: nat := a1 / 10;
  var a3: nat := a2 / 10;
  var a4: nat := a3 / 10;
  var a5: nat := a4 / 10;
  var a6: nat := a5 / 10;
  var a7: nat := a6 / 10;
  var a8: nat := a7 / 10;
  var a9: nat := a8 / 10;

  if y >= 1000000000 {
    n := 10;
    assert 100000000 <= a1 < 1000000000;
    assert 10000000 <= a2 < 100000000;
    assert 1000000 <= a3 < 10000000;
    assert 100000 <= a4 < 1000000;
    assert 10000 <= a5 < 100000;
    assert 1000 <= a6 < 10000;
    assert 100 <= a7 < 1000;
    assert 10 <= a8 < 100;
    assert 0 <= a9 <= 9;
    assert digits(a9) == 1;
    assert digits(a8) == 1 + digits(a9);
    assert digits(a8) == 2;
    assert digits(a7) == 1 + digits(a8);
    assert digits(a7) == 3;
    assert digits(a6) == 1 + digits(a7);
    assert digits(a6) == 4;
    assert digits(a5) == 1 + digits(a6);
    assert digits(a5) == 5;
    assert digits(a4) == 1 + digits(a5);
    assert digits(a4) == 6;
    assert digits(a3) == 1 + digits(a4);
    assert digits(a3) == 7;
    assert digits(a2) == 1 + digits(a3);
    assert digits(a2) == 8;
    assert digits(a1) == 1 + digits(a2);
    assert digits(a1) == 9;
    assert digits(a0) == 1 + digits(a1);
    assert digits(a0) == 10;
    assert n == digits(a0);
  } else if y >= 100000000 {
    n := 9;
    assert 10000000 <= a1 < 100000000;
    assert 1000000 <= a2 < 10000000;
    assert 100000 <= a3 < 1000000;
    assert 10000 <= a4 < 100000;
    assert 1000 <= a5 < 10000;
    assert 100 <= a6 < 1000;
    assert 10 <= a7 < 100;
    assert 0 <= a8 <= 9;
    assert digits(a8) == 1;
    assert digits(a7) == 1 + digits(a8);
    assert digits(a7) == 2;
    assert digits(a6) == 1 + digits(a7);
    assert digits(a6) == 3;
    assert digits(a5) == 1 + digits(a6);
    assert digits(a5) == 4;
    assert digits(a4) == 1 + digits(a5);
    assert digits(a4) == 5;
    assert digits(a3) == 1 + digits(a4);
    assert digits(a3) == 6;
    assert digits(a2) == 1 + digits(a3);
    assert digits(a2) == 7;
    assert digits(a1) == 1 + digits(a2);
    assert digits(a1) == 8;
    assert digits(a0) == 1 + digits(a1);
    assert digits(a0) == 9;
    assert n == digits(a0);
  } else if y >= 10000000 {
    n := 8;
    assert 1000000 <= a1 < 10000000;
    assert 100000 <= a2 < 1000000;
    assert 10000 <= a3 < 100000;
    assert 1000 <= a4 < 10000;
    assert 100 <= a5 < 1000;
    assert 10 <= a6 < 100;
    assert 0 <= a7 <= 9;
    assert digits(a7) == 1;
    assert digits(a6) == 1 + digits(a7);
    assert digits(a6) == 2;
    assert digits(a5) == 1 + digits(a6);
    assert digits(a5) == 3;
    assert digits(a4) == 1 + digits(a5);
    assert digits(a4) == 4;
    assert digits(a3) == 1 + digits(a4);
    assert digits(a3) == 5;
    assert digits(a2) == 1 + digits(a3);
    assert digits(a2) == 6;
    assert digits(a1) == 1 + digits(a2);
    assert digits(a1) == 7;
    assert digits(a0) == 1 + digits(a1);
    assert digits(a0) == 8;
    assert n == digits(a0);
  } else if y >= 1000000 {
    n := 7;
    assert 100000 <= a1 < 1000000;
    assert 10000 <= a2 < 100000;
    assert 1000 <= a3 < 10000;
    assert 100 <= a4 < 1000;
    assert 10 <= a5 < 100;
    assert 0 <= a6 <= 9;
    assert digits(a6) == 1;
    assert digits(a5) == 1 + digits(a6);
    assert digits(a5) == 2;
    assert digits(a4) == 1 + digits(a5);
    assert digits(a4) == 3;
    assert digits(a3) == 1 + digits(a4);
    assert digits(a3) == 4;
    assert digits(a2) == 1 + digits(a3);
    assert digits(a2) == 5;
    assert digits(a1) == 1 + digits(a2);
    assert digits(a1) == 6;
    assert digits(a0) == 1 + digits(a1);
    assert digits(a0) == 7;
    assert n == digits(a0);
  } else if y >= 100000 {
    n := 6;
    assert 10000 <= a1 < 100000;
    assert 1000 <= a2 < 10000;
    assert 100 <= a3 < 1000;
    assert 10 <= a4 < 100;
    assert 0 <= a5 <= 9;
    assert digits(a5) == 1;
    assert digits(a4) == 1 + digits(a5);
    assert digits(a4) == 2;
    assert digits(a3) == 1 + digits(a4);
    assert digits(a3) == 3;
    assert digits(a2) == 1 + digits(a3);
    assert digits(a2) == 4;
    assert digits(a1) == 1 + digits(a2);
    assert digits(a1) == 5;
    assert digits(a0) == 1 + digits(a1);
    assert digits(a0) == 6;
    assert n == digits(a0);
  } else if y >= 10000 {
    n := 5;
    assert 1000 <= a1 < 10000;
    assert 100 <= a2 < 1000;
    assert 10 <= a3 < 100;
    assert 0 <= a4 <= 9;
    assert digits(a4) == 1;
    assert digits(a3) == 1 + digits(a4);
    assert digits(a3) == 2;
    assert digits(a2) == 1 + digits(a3);
    assert digits(a2) == 3;
    assert digits(a1) == 1 + digits(a2);
    assert digits(a1) == 4;
    assert digits(a0) == 1 + digits(a1);
    assert digits(a0) == 5;
    assert n == digits(a0);
  } else if y >= 1000 {
    n := 4;
    assert 100 <= a1 < 1000;
    assert 10 <= a2 < 100;
    assert 0 <= a3 <= 9;
    assert digits(a3) == 1;
    assert digits(a2) == 1 + digits(a3);
    assert digits(a2) == 2;
    assert digits(a1) == 1 + digits(a2);
    assert digits(a1) == 3;
    assert digits(a0) == 1 + digits(a1);
    assert digits(a0) == 4;
    assert n == digits(a0);
  } else if y >= 100 {
    n := 3;
    assert 10 <= a1 < 100;
    assert 0 <= a2 <= 9;
    assert digits(a2) == 1;
    assert digits(a1) == 1 + digits(a2);
    assert digits(a1) == 2;
    assert digits(a0) == 1 + digits(a1);
    assert digits(a0) == 3;
    assert n == digits(a0);
  } else if y >= 10 {
    n := 2;
    assert 0 <= a1 <= 9;
    assert digits(a1) == 1;
    assert digits(a0) == 1 + digits(a1);
    assert digits(a0) == 2;
    assert n == digits(a0);
  } else {
    n := 1;
    assert 0 <= a0 <= 9;
    assert digits(a0) == 1;
    assert n == digits(a0);
  }

  assert a0 == y;
  assert n == digits(y);
  if i < 0 {
    assert x == -i;
    assert y == -i;
    assert n == digits(-i);
  } else {
    assert x == i;
    assert y == i;
    assert n == digits(i);
  }
}