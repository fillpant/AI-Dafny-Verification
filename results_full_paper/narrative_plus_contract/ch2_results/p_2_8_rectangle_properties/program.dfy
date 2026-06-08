method p_2_8_rectangle_properties(length: real, width: real) returns (area: real, perimeter: real, diagonal: real)
	ensures area == length * width
	ensures perimeter == 2.0 * (length + width)
	ensures -0.01 < (diagonal * diagonal) - ((length * length) + (width * width)) < 0.01
{
  area := length * width;
  perimeter := 2.0 * (length + width);

  var s := length * length + width * width;
  assert 0.0 <= length * length;
  assert 0.0 <= width * width;
  assert 0.0 <= s;

  var hi := 1.0;
  while hi * hi <= s
    invariant 1.0 <= hi
    invariant 0.0 <= s
    decreases s - hi
  {
    assert hi <= hi * hi;
    assert hi <= s;
    hi := 2.0 * hi;
  }

  var lo := 0.0;
  var H := hi;
  var factor := 1.0;
  var target := 256.0 * H * H;

  while factor < target
    invariant 1.0 <= H
    invariant 1.0 <= factor
    invariant 0.0 <= lo <= hi <= H
    invariant lo * lo <= s < hi * hi
    invariant (hi - lo) * factor <= H
    invariant target == 256.0 * H * H
    decreases target - factor
  {
    var oldLo := lo;
    var oldHi := hi;
    var oldFactor := factor;
    var mid := (oldLo + oldHi) / 2.0;

    assert oldLo <= mid <= oldHi;
    if mid * mid <= s {
      lo := mid;
    } else {
      hi := mid;
    }

    assert hi - lo == (oldHi - oldLo) / 2.0;
    factor := 2.0 * oldFactor;
    assert (hi - lo) * factor == (oldHi - oldLo) * oldFactor;
  }

  assert target <= factor;
  assert 0.0 <= hi - lo;
  assert (hi - lo) * target <= (hi - lo) * factor;
  assert (hi - lo) * target <= H;
  assert 0.0 < H;
  assert target == 256.0 * H * H;
  assert ((hi - lo) * 256.0 * H) * H == (hi - lo) * target;
  assert (hi - lo) * 256.0 * H <= 1.0;
  assert hi + lo <= 2.0 * H;
  assert (hi - lo) * (hi + lo) <= (hi - lo) * (2.0 * H);
  assert (hi - lo) * (hi + lo) <= 1.0 / 128.0;
  assert 1.0 / 128.0 < 0.01;
  assert hi * hi - lo * lo == (hi - lo) * (hi + lo);
  assert hi * hi - lo * lo < 0.01;

  diagonal := lo;
  assert diagonal * diagonal <= s;
  assert s < hi * hi;
  assert s - diagonal * diagonal < 0.01;
  assert -0.01 < diagonal * diagonal - s;
  assert diagonal * diagonal - s < 0.01;
}