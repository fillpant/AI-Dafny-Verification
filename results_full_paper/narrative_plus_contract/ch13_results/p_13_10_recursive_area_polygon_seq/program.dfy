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

method p_13_10_recursive_area_polygon_seq(points: seq<(real, real)>) returns (area: real)
	requires |points| >= 3
	ensures area == polygon_area(points)
{
  var cur := points;
  var acc: real := 0.0;

  assert acc + polygon_area(cur) == polygon_area(points);

  while |cur| > 3
    invariant |cur| >= 3
    invariant acc + polygon_area(cur) == polygon_area(points)
    decreases |cur|
  {
    var (x1, y1) := cur[0];
    var (x2, y2) := cur[1];
    var (x3, y3) := cur[2];
    var sign: real := x1 * (y2 - y3) + x2 * (y3 - y1) + x3 * (y1 - y2);
    var triangle_area: real := if sign < 0.0 then -sign / 2.0 else sign / 2.0;

    var rest := [cur[0]] + cur[2..];
    assert |cur[2..]| == |cur| - 2;
    assert |[cur[0]]| == 1;
    assert |rest| == |[cur[0]]| + |cur[2..]|;
    assert |rest| == |cur| - 1;
    assert |rest| >= 3;
    assert |rest| < |cur|;
    assert |cur| != 3;

    assert polygon_area(cur) == triangle_area + polygon_area(rest);
    assert acc + (triangle_area + polygon_area(rest)) == polygon_area(points);
    assert acc + triangle_area + polygon_area(rest) == polygon_area(points);

    acc := acc + triangle_area;
    cur := rest;
    assert acc + polygon_area(cur) == polygon_area(points);
  }

  assert |cur| == 3;
  var (x1, y1) := cur[0];
  var (x2, y2) := cur[1];
  var (x3, y3) := cur[2];
  var sign: real := x1 * (y2 - y3) + x2 * (y3 - y1) + x3 * (y1 - y2);
  var triangle_area: real := if sign < 0.0 then -sign / 2.0 else sign / 2.0;

  assert polygon_area(cur) == triangle_area;
  assert acc + triangle_area == polygon_area(points);
  area := acc + triangle_area;
}