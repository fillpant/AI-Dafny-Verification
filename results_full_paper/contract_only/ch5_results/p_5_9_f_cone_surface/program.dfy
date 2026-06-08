method p_5_9_f_cone_surface(r: real, h: real) returns (surface: real)
	requires r > 0.0
	ensures -0.01 < (((surface / (3.14159 * r)) - r) * ((surface / (3.14159 * r)) - r)) - ((h * h) + (r * r)) < 0.01
{
  var S := h * h + r * r;
  assert h * h >= 0.0;
  assert r * r > 0.0;
  assert S >= 0.0;

  var lo := 0.0;
  var hi := S + 1.0;

  assert lo * lo <= S;
  assert S * S >= 0.0;
  calc {
    hi * hi - S;
    ==
    (S + 1.0) * (S + 1.0) - S;
    ==
    S * S + S + 1.0;
  }
  assert hi * hi - S >= 0.0;
  assert S <= hi * hi;

  while 0.01 <= (hi - lo) * (hi + lo)
    invariant 0.0 <= lo <= hi
    invariant lo * lo <= S <= hi * hi
    decreases hi - lo
  {
    var oldLo := lo;
    var oldHi := hi;
    var width := oldHi - oldLo;

    assert width >= 0.0;
    assert oldHi + oldLo >= 0.0;
    if width == 0.0 {
      assert (hi - lo) * (hi + lo) == 0.0;
      assert false;
    }
    assert width > 0.0;

    var mid := (oldLo + oldHi) / 2.0;
    assert mid - oldLo == width / 2.0;
    assert oldHi - mid == width / 2.0;
    assert width / 2.0 > 0.0;
    assert oldLo < mid < oldHi;

    if mid * mid <= S {
      lo := mid;
      assert hi == oldHi;
      assert lo * lo <= S;
      assert S <= hi * hi;
      assert hi - lo == width / 2.0;
    } else {
      hi := mid;
      assert lo == oldLo;
      assert S <= hi * hi;
      assert lo * lo <= S;
      assert hi - lo == width / 2.0;
    }

    assert hi - lo == width / 2.0;
    assert width / 2.0 < width;
    assert hi - lo < width;
    assert width == oldHi - oldLo;
    assert hi - lo < oldHi - oldLo;
  }

  assert (hi - lo) * (hi + lo) < 0.01;
  calc {
    hi * hi - lo * lo;
    ==
    (hi - lo) * (hi + lo);
  }
  assert S - lo * lo <= hi * hi - lo * lo;
  assert S - lo * lo < 0.01;
  assert lo * lo - S <= 0.0;
  assert -0.01 < lo * lo - S;
  assert lo * lo - S < 0.01;

  var den := 3.14159 * r;
  assert den > 0.0;
  assert den != 0.0;

  surface := den * (r + lo);

  assert den == 3.14159 * r;
  assert surface / den == r + lo;
  assert surface / (3.14159 * r) == r + lo;
  assert (surface / (3.14159 * r)) - r == lo;
  assert (((surface / (3.14159 * r)) - r) * ((surface / (3.14159 * r)) - r)) - ((h * h) + (r * r)) == lo * lo - S;
  assert -0.01 < (((surface / (3.14159 * r)) - r) * ((surface / (3.14159 * r)) - r)) - ((h * h) + (r * r)) < 0.01;
}