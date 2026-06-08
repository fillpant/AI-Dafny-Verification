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
  var original := points[..];
  var s := original;
  area := 0.0;

  assert |original| == points.Length;
  assert |original| >= 3;

  while |s| > 3
    invariant |original| >= 3
    invariant |s| >= 3
    invariant original == points[..]
    invariant area + polygon_area(s) == polygon_area(original)
    decreases |s|
  {
    var (x1, y1) := s[0];
    var (x2, y2) := s[1];
    var (x3, y3) := s[2];
    var sign: real := x1 * (y2 - y3) + x2 * (y3 - y1) + x3 * (y1 - y2);
    var triangle_area: real := if sign < 0.0 then -sign / 2.0 else sign / 2.0;

    var t := [s[0]] + s[2..];
    assert |[s[0]]| == 1;
    assert |s[2..]| == |s| - 2;
    assert |t| == |[s[0]]| + |s[2..]|;
    assert |t| == |s| - 1;
    assert |t| >= 3;
    assert |s| != 3;
    assert s[0] == (x1, y1);
    assert s[1] == (x2, y2);
    assert s[2] == (x3, y3);
    assert t == [s[0]] + s[2..];

    assert polygon_area(s) == triangle_area + polygon_area(t) by {
      if sign < 0.0 {
        assert triangle_area == -sign / 2.0;
        assert polygon_area(s) == -sign / 2.0 + polygon_area([s[0]] + s[2..]);
      } else {
        assert triangle_area == sign / 2.0;
        assert polygon_area(s) == sign / 2.0 + polygon_area([s[0]] + s[2..]);
      }
      assert t == [s[0]] + s[2..];
    }

    var oldArea := area;
    assert oldArea + polygon_area(s) == polygon_area(original);
    calc {
      oldArea + triangle_area + polygon_area(t);
      ==
      oldArea + (triangle_area + polygon_area(t));
      == {
        assert polygon_area(s) == triangle_area + polygon_area(t);
      }
      oldArea + polygon_area(s);
      == {
        assert oldArea + polygon_area(s) == polygon_area(original);
      }
      polygon_area(original);
    }

    area := oldArea + triangle_area;
    assert area + polygon_area(t) == polygon_area(original);
    s := t;
  }

  assert |s| == 3;
  var (x1, y1) := s[0];
  var (x2, y2) := s[1];
  var (x3, y3) := s[2];
  var sign: real := x1 * (y2 - y3) + x2 * (y3 - y1) + x3 * (y1 - y2);
  var triangle_area: real := if sign < 0.0 then -sign / 2.0 else sign / 2.0;
  assert s[0] == (x1, y1);
  assert s[1] == (x2, y2);
  assert s[2] == (x3, y3);

  assert polygon_area(s) == triangle_area by {
    if sign < 0.0 {
      assert triangle_area == -sign / 2.0;
      assert polygon_area(s) == -sign / 2.0;
    } else {
      assert triangle_area == sign / 2.0;
      assert polygon_area(s) == sign / 2.0;
    }
  }

  var oldArea := area;
  assert oldArea + polygon_area(s) == polygon_area(original);
  calc {
    oldArea + triangle_area;
    == {
      assert polygon_area(s) == triangle_area;
    }
    oldArea + polygon_area(s);
    == {
      assert oldArea + polygon_area(s) == polygon_area(original);
    }
    polygon_area(original);
  }

  area := oldArea + triangle_area;
  assert area == polygon_area(original);
  assert original == points[..];
}