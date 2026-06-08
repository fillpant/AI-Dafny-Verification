function polygon_area(points: seq<(real, real)>): real
  decreases |points|
  requires |points| >= 3
  ensures polygon_area(points) >= 0.0
{
  if |points| == 3 then 
    var (x1, y1) := points[0];
    var (x2, y2) := points[1];
    var (x3, y3) := points[2];
    var sign : real := x1 * (y2 - y3) + x2 * (y3 - y1) + x3 * (y1 - y2);
    if sign < 0.0 then -sign / 2.0 else sign / 2.0 as real 
  else 
    var (x1, y1) := points[0];
    var (x2, y2) := points[1];
    var (x3, y3) := points[2];
    var sign : real := x1 * (y2 - y3) + x2 * (y3 - y1) + x3 * (y1 - y2);
    var triangle_area := if sign < 0.0 then -sign / 2.0 else sign / 2.0 as real;
    triangle_area + polygon_area([points[0]] + points[2..])
}

method p_13_10_recursive_area_polygon_array(points: array<(real, real)>) returns (area: real)
	requires points.Length >= 3
	ensures area == polygon_area(points[..])
{
  var n := points.Length;
  area := 0.0;
  var i := 1;

  assert points[..] == [points[0]] + points[1..];

  while i < n - 2
    invariant n == points.Length
    invariant 3 <= n
    invariant 1 <= i <= n - 2
    invariant |[points[0]] + points[i..]| >= 3
    invariant area + polygon_area([points[0]] + points[i..]) == polygon_area(points[..])
    decreases n - i
  {
    assert 0 <= i < n;
    assert 0 <= i + 1 <= n;

    ghost var tail := points[i..];
    assert |tail| == n - i;
    assert 1 <= |tail|;
    assert tail == tail[..1] + tail[1..];
    assert |tail[..1]| == 1;
    assert tail[..1][0] == points[i];
    assert tail[..1] == [points[i]];
    assert |tail[1..]| == |points[i + 1..]|;
    forall k | 0 <= k < |tail[1..]|
      ensures tail[1..][k] == points[i + 1..][k]
    {
      assert tail[1..][k] == tail[1 + k];
      assert tail[1 + k] == points[i + 1 + k];
      assert points[i + 1..][k] == points[i + 1 + k];
    }
    assert tail[1..] == points[i + 1..];
    assert points[i..] == [points[i]] + points[i + 1..];

    var (x1, y1) := points[0];
    var (x2, y2) := points[i];
    var (x3, y3) := points[i + 1];
    var sign: real := x1 * (y2 - y3) + x2 * (y3 - y1) + x3 * (y1 - y2);
    var triangle_area := if sign < 0.0 then -sign / 2.0 else sign / 2.0;

    ghost var rem := [points[0]] + points[i..];
    assert rem == [points[0]] + ([points[i]] + points[i + 1..]);
    assert |rem| == 1 + n - i;
    assert |rem| > 3;
    assert rem[0] == points[0];
    assert rem[1] == points[i];
    assert rem[2] == points[i + 1];

    assert |rem[2..]| == |points[i + 1..]|;
    forall k | 0 <= k < |rem[2..]|
      ensures rem[2..][k] == points[i + 1..][k]
    {
      assert rem[2..][k] == rem[2 + k];
      assert rem[2 + k] == ([points[i]] + points[i + 1..])[1 + k];
      assert ([points[i]] + points[i + 1..])[1 + k] == points[i + 1..][k];
    }
    assert rem[2..] == points[i + 1..];
    assert [rem[0]] + rem[2..] == [points[0]] + points[i + 1..];
    assert |[rem[0]] + rem[2..]| >= 3;

    ghost var (rx1, ry1) := rem[0];
    ghost var (rx2, ry2) := rem[1];
    ghost var (rx3, ry3) := rem[2];
    ghost var rsign: real := rx1 * (ry2 - ry3) + rx2 * (ry3 - ry1) + rx3 * (ry1 - ry2);
    ghost var rtri := if rsign < 0.0 then -rsign / 2.0 else rsign / 2.0;
    assert rem[0] == (rx1, ry1);
    assert rem[1] == (rx2, ry2);
    assert rem[2] == (rx3, ry3);
    assert rsign == sign;
    assert rtri == triangle_area;
    assert |rem| != 3;
    assert polygon_area(rem) == (if |rem| == 3 then rtri else rtri + polygon_area([rem[0]] + rem[2..]));
    assert polygon_area(rem) == rtri + polygon_area([rem[0]] + rem[2..]);
    assert polygon_area(rem) == triangle_area + polygon_area([points[0]] + points[i + 1..]);
    assert area + triangle_area + polygon_area([points[0]] + points[i + 1..]) == polygon_area(points[..]);

    area := area + triangle_area;
    i := i + 1;
    assert area + polygon_area([points[0]] + points[i..]) == polygon_area(points[..]);
  }

  assert i == n - 2;
  assert 0 <= i < n;
  assert 0 <= i + 1 < n;

  ghost var tail := points[i..];
  assert |tail| == 2;
  assert tail[0] == points[i];
  assert tail[1] == points[i + 1];

  var (x1, y1) := points[0];
  var (x2, y2) := points[i];
  var (x3, y3) := points[i + 1];
  var sign: real := x1 * (y2 - y3) + x2 * (y3 - y1) + x3 * (y1 - y2);
  var triangle_area := if sign < 0.0 then -sign / 2.0 else sign / 2.0;

  ghost var rem := [points[0]] + points[i..];
  assert |rem| == 3;
  assert rem[0] == points[0];
  assert rem[1] == points[i];
  assert rem[2] == points[i + 1];

  ghost var (rx1, ry1) := rem[0];
  ghost var (rx2, ry2) := rem[1];
  ghost var (rx3, ry3) := rem[2];
  ghost var rsign: real := rx1 * (ry2 - ry3) + rx2 * (ry3 - ry1) + rx3 * (ry1 - ry2);
  ghost var rtri := if rsign < 0.0 then -rsign / 2.0 else rsign / 2.0;
  assert rem[0] == (rx1, ry1);
  assert rem[1] == (rx2, ry2);
  assert rem[2] == (rx3, ry3);
  assert rsign == sign;
  assert rtri == triangle_area;
  assert polygon_area(rem) == (if |rem| == 3 then rtri else rtri + polygon_area([rem[0]] + rem[2..]));
  assert polygon_area(rem) == rtri;
  assert polygon_area(rem) == triangle_area;
  assert area + triangle_area == polygon_area(points[..]);
  area := area + triangle_area;
}