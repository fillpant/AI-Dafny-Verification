method p_5_9_f_cone_surface(r: real, h: real) returns (surface: real)
	requires r > 0.0
	ensures -0.01 < (((surface / (3.14159 * r)) - r) * ((surface / (3.14159 * r)) - r)) - ((h * h) + (r * r)) < 0.01
{
  var S := h * h + r * r;
  assert 0.0 <= h * h;
  assert 0.0 < r * r;
  assert 0.0 < S;

  var lo := 0.0;
  var hi := S + 1.0;

  assert 0.0 <= S * S;
  assert hi * hi - S == S * S + S + 1.0;
  assert 0.0 <= hi * hi - S;
  assert S <= hi * hi;

  while 0.01 <= hi * hi - lo * lo
    invariant 0.0 <= lo <= hi
    invariant lo * lo <= S <= hi * hi
    decreases hi - lo
  {
    assert 0.0 < hi * hi - lo * lo;
    assert lo < hi;
    assert 0.0 < hi - lo;

    ghost var oldLo := lo;
    ghost var oldHi := hi;
    var mid := (lo + hi) / 2.0;

    assert oldLo <= mid <= oldHi;
    assert mid - oldLo == (oldHi - oldLo) / 2.0;
    assert oldHi - mid == (oldHi - oldLo) / 2.0;

    if mid * mid <= S {
      lo := mid;
      assert 0.0 <= lo <= hi;
      assert lo * lo <= S <= hi * hi;
      assert hi - lo == (oldHi - oldLo) / 2.0;
      assert hi - lo < oldHi - oldLo;
    } else {
      hi := mid;
      assert 0.0 <= lo <= hi;
      assert lo * lo <= S <= hi * hi;
      assert hi - lo == (oldHi - oldLo) / 2.0;
      assert hi - lo < oldHi - oldLo;
    }
  }

  assert hi * hi - lo * lo < 0.01;
  assert lo * lo <= S <= hi * hi;
  assert lo * lo - S <= 0.0;
  assert lo * lo - S < 0.01;
  assert S - lo * lo <= hi * hi - lo * lo;
  assert S - lo * lo < 0.01;
  assert -0.01 < lo * lo - S;

  var q := 3.14159 * r;
  assert 3.14159 > 0.0;
  assert q > 0.0;
  assert q != 0.0;

  surface := q * (r + lo);

  assert surface == q * (r + lo);
  assert q * (surface / q) == surface;
  assert q * ((surface / q) - (r + lo)) == 0.0;
  assert (surface / q) - (r + lo) == 0.0;
  assert surface / q == r + lo;
  assert q == 3.14159 * r;
  assert surface / (3.14159 * r) == r + lo;
  assert (surface / (3.14159 * r)) - r == lo;
  assert (((surface / (3.14159 * r)) - r) * ((surface / (3.14159 * r)) - r)) - ((h * h) + (r * r)) == lo * lo - S;
  assert -0.01 < (((surface / (3.14159 * r)) - r) * ((surface / (3.14159 * r)) - r)) - ((h * h) + (r * r)) < 0.01;
}