method p_5_9_f_cone_surface(r: real, h: real) returns (surface: real)
	requires r > 0.0
	ensures -0.01 < (((surface / (3.14159 * r)) - r) * ((surface / (3.14159 * r)) - r)) - ((h * h) + (r * r)) < 0.01
{
  var hh := h * h;
  var rr := r * r;
  assert hh >= 0.0;
  assert rr > 0.0;
  var y := hh + rr;
  assert y >= rr;
  assert y > 0.0;
  assert y == h * h + r * r;

  var x := if y >= 1.0 then y else 1.0;
  if y >= 1.0 {
    assert x == y;
    assert y > 0.0;
    assert y * y >= y;
    assert x * x >= y;
    assert x > 0.0;
  } else {
    assert x == 1.0;
    assert y < 1.0;
    assert x * x == 1.0;
    assert x * x >= y;
    assert x > 0.0;
  }

  while x * x - y >= 0.01
    invariant y > 0.0
    invariant y == h * h + r * r
    invariant x > 0.0
    invariant x * x >= y
    decreases 100000.0 * (x * x - y)
  {
    var oldX := x;
    var e := oldX * oldX - y;
    assert e >= 0.01;
    assert e > 0.0;
    assert oldX > 0.0;
    assert oldX * oldX >= y;
    assert e == oldX * oldX - y;
    assert e < oldX * oldX;
    assert 2.0 * oldX > 0.0;

    var d := e / (2.0 * oldX);
    assert d > 0.0;
    assert 2.0 * oldX * d == e;
    assert d < oldX / 2.0;
    assert d * d < d * oldX / 2.0;
    assert d * oldX / 2.0 == e / 4.0;
    assert d * d < e / 4.0;

    x := oldX - d;
    assert x > 0.0;
    calc {
      x * x - y;
    ==
      (oldX - d) * (oldX - d) - y;
    ==
      oldX * oldX - 2.0 * oldX * d + d * d - y;
    ==
      e - 2.0 * oldX * d + d * d;
    ==
      d * d;
    }
    assert x * x - y == d * d;
    assert x * x >= y;
    assert x * x - y < e / 4.0;
    assert 100000.0 * (x * x - y) < 25000.0 * e;
    assert 25000.0 * e <= 100000.0 * e - 1.0;
    assert 100000.0 * (x * x - y) < 100000.0 * e - 1.0;
  }

  assert x * x - y >= 0.0;
  assert x * x - y < 0.01;

  var denom := 3.14159 * r;
  assert 3.14159 > 0.0;
  assert denom > 0.0;
  assert denom != 0.0;

  surface := denom * (r + x);
  assert surface == denom * (r + x);
  assert surface / denom == r + x;
  assert denom == 3.14159 * r;
  assert surface / (3.14159 * r) == r + x;
  assert (surface / (3.14159 * r)) - r == x;
  assert ((surface / (3.14159 * r)) - r) * ((surface / (3.14159 * r)) - r) == x * x;
  assert (((surface / (3.14159 * r)) - r) * ((surface / (3.14159 * r)) - r)) - ((h * h) + (r * r)) == x * x - y;
  assert -0.01 < x * x - y;
  assert x * x - y < 0.01;
}