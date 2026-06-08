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
  var acc: real := 0.0;
  var q := points;
  assert acc + polygon_area(q) == polygon_area(points);

  while |q| > 3
    invariant |q| >= 3
    invariant acc + polygon_area(q) == polygon_area(points)
    decreases |q|
  {
    var sign: real := (q[0]).0 * ((q[1]).1 - (q[2]).1) + (q[1]).0 * ((q[2]).1 - (q[0]).1) + (q[2]).0 * ((q[0]).1 - (q[1]).1);
    var triangle_area: real := if sign < 0.0 then -sign / 2.0 else sign / 2.0;

    var qNext := [q[0]] + q[2..];
    assert |q[2..]| == |q| - 2;
    assert |qNext| == |q| - 1;
    assert |qNext| >= 3;
    assert qNext == [q[0]] + q[2..];

    assert polygon_area(q) == triangle_area + polygon_area(qNext) by {
      reveal polygon_area();
      assert |q| != 3;
      assert qNext == [q[0]] + q[2..];
    }

    var newAcc := acc + triangle_area;
    assert newAcc + polygon_area(qNext) == acc + (triangle_area + polygon_area(qNext));
    assert newAcc + polygon_area(qNext) == acc + polygon_area(q);
    assert newAcc + polygon_area(qNext) == polygon_area(points);

    acc := newAcc;
    q := qNext;
  }

  assert |q| == 3;
  var sign: real := (q[0]).0 * ((q[1]).1 - (q[2]).1) + (q[1]).0 * ((q[2]).1 - (q[0]).1) + (q[2]).0 * ((q[0]).1 - (q[1]).1);
  var triangle_area: real := if sign < 0.0 then -sign / 2.0 else sign / 2.0;

  assert polygon_area(q) == triangle_area by {
    reveal polygon_area();
    assert |q| == 3;
  }

  area := acc + triangle_area;
  assert area == acc + polygon_area(q);
  assert area == polygon_area(points);
}