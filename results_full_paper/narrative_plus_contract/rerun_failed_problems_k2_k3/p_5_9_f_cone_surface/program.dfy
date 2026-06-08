method p_5_9_f_cone_surface(r: real, h: real) returns (surface: real)
	requires r > 0.0
	ensures -0.01 < (((surface / (3.14159 * r)) - r) * ((surface / (3.14159 * r)) - r)) - ((h * h) + (r * r)) < 0.01
{
  var y := h * h + r * r;

  assert h * h >= 0.0;
  assert r * r > 0.0;
  assert h * h + r * r >= r * r;
  assert h * h + r * r > 0.0;
  assert y > 0.0;
  assert y >= 0.0;

  var low := 0.0;
  var high := y + 1.0;

  assert low * low <= y;
  assert high > 0.0;
  assert low <= high;
  assert y * y >= 0.0;
  assert (y + 1.0) * (y + 1.0) - y == y * y + y + 1.0;
  assert (y + 1.0) * (y + 1.0) >= y;
  assert y <= high * high;

  while high * high - low * low >= 0.01
    invariant 0.0 <= low
    invariant low <= high
    invariant high > 0.0
    invariant low * low <= y
    invariant y <= high * high
    decreases high - low
  {
    var oldLow := low;
    var oldHigh := high;
    var mid := (oldLow + oldHigh) / 2.0;

    assert oldHigh * oldHigh - oldLow * oldLow >= 0.01;
    assert oldHigh * oldHigh - oldLow * oldLow > 0.0;
    if oldLow == oldHigh {
      assert oldHigh * oldHigh - oldLow * oldLow == 0.0;
      assert false;
    }
    assert oldLow < oldHigh;
    assert mid == oldLow + (oldHigh - oldLow) / 2.0;
    assert oldLow < mid;
    assert mid < oldHigh;
    assert mid > 0.0;

    if mid * mid <= y {
      low := mid;
      assert low * low <= y;
      assert y <= high * high;
    } else {
      high := mid;
      assert y < high * high;
      assert y <= high * high;
      assert low * low <= y;
    }

    assert high - low == (oldHigh - oldLow) / 2.0;
    assert oldHigh - oldLow > 0.0;
    assert (oldHigh - oldLow) / 2.0 < oldHigh - oldLow;
    assert high - low < oldHigh - oldLow;
  }

  assert high * high - low * low < 0.01;
  assert high * high - y >= 0.0;
  assert high * high - y <= high * high - low * low;
  assert high * high - y < 0.01;

  var denom := 3.14159 * r;
  var z := r + high;
  surface := denom * z;

  assert 3.14159 > 0.0;
  assert denom > 0.0;
  assert denom != 0.0;
  assert denom / denom == 1.0;
  assert (denom * z) / denom == (denom / denom) * z;
  assert (denom * z) / denom == z;
  assert surface / denom == z;
  assert denom == 3.14159 * r;
  assert surface / (3.14159 * r) == z;
  assert (surface / (3.14159 * r)) - r == high;
  assert (((surface / (3.14159 * r)) - r) * ((surface / (3.14159 * r)) - r)) - ((h * h) + (r * r)) == high * high - y;
  assert -0.01 < high * high - y;
  assert high * high - y < 0.01;
}