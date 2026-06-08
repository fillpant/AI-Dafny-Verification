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
  var total: real := 0.0;
  var k: int := 1;

  assert |[points[0]] + points[1..]| == |points[..]|;
  forall j | 0 <= j < |points[..]|
    ensures ([points[0]] + points[1..])[j] == points[..][j]
  {
    if j == 0 {
      assert ([points[0]] + points[1..])[j] == points[0];
      assert points[..][j] == points[0];
    } else {
      assert 0 <= j - 1 < |points[1..]|;
      assert ([points[0]] + points[1..])[j] == points[1..][j - 1];
      assert points[1..][j - 1] == points[j];
      assert points[..][j] == points[j];
    }
  }
  assert [points[0]] + points[1..] == points[..];

  while k < points.Length - 2
    invariant 1 <= k <= points.Length - 2
    invariant total + polygon_area([points[0]] + points[k..]) == polygon_area(points[..])
    decreases points.Length - 2 - k
  {
    var oldTail := [points[0]] + points[k..];
    assert |oldTail| > 3;
    assert oldTail[0] == points[0];
    assert oldTail[1] == points[k];
    assert oldTail[2] == points[k + 1];

    var (sx1, sy1) := oldTail[0];
    var (sx2, sy2) := oldTail[1];
    var (sx3, sy3) := oldTail[2];
    var ssign: real := sx1 * (sy2 - sy3) + sx2 * (sy3 - sy1) + sx3 * (sy1 - sy2);
    var stri: real := if ssign < 0.0 then -ssign / 2.0 else ssign / 2.0;

    var newTail := [points[0]] + points[k + 1..];

    assert |oldTail[2..]| == |points[k + 1..]|;
    forall j | 0 <= j < |oldTail[2..]|
      ensures oldTail[2..][j] == points[k + 1..][j]
    {
      assert oldTail[2..][j] == oldTail[j + 2];
      assert 0 < j + 2 < |oldTail|;
      assert oldTail[j + 2] == points[k..][j + 1];
      assert 0 <= j + 1 < |points[k..]|;
      assert points[k..][j + 1] == points[k + j + 1];
      assert points[k + 1..][j] == points[k + 1 + j];
      assert k + j + 1 == k + 1 + j;
    }
    assert oldTail[2..] == points[k + 1..];
    assert [oldTail[0]] + oldTail[2..] == newTail;

    assert polygon_area(oldTail) == stri + polygon_area([oldTail[0]] + oldTail[2..]);
    assert polygon_area(oldTail) == stri + polygon_area(newTail);
    assert total + polygon_area(oldTail) == polygon_area(points[..]);
    assert total + stri + polygon_area(newTail) == polygon_area(points[..]);

    total := total + stri;
    k := k + 1;
    assert [points[0]] + points[k..] == newTail;
    assert total + polygon_area([points[0]] + points[k..]) == polygon_area(points[..]);
  }

  assert k == points.Length - 2;
  var tail := [points[0]] + points[k..];
  assert |tail| == 3;
  assert tail[0] == points[0];
  assert tail[1] == points[k];
  assert tail[2] == points[k + 1];

  var (tx1, ty1) := tail[0];
  var (tx2, ty2) := tail[1];
  var (tx3, ty3) := tail[2];
  var tsign: real := tx1 * (ty2 - ty3) + tx2 * (ty3 - ty1) + tx3 * (ty1 - ty2);
  var ttri: real := if tsign < 0.0 then -tsign / 2.0 else tsign / 2.0;

  assert polygon_area(tail) == ttri;
  area := total + ttri;
  assert area == polygon_area(points[..]);
}