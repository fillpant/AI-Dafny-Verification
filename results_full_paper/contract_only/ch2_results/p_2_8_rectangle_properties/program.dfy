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

  assert exists d: real {:trigger d * d} :: d * d == s;
  diagonal :| diagonal * diagonal == s;

  assert (diagonal * diagonal) - s == 0.0;
  assert -0.01 < 0.0;
  assert 0.0 < 0.01;
}