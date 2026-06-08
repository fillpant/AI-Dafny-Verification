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

  ghost var initial := [points[0]] + points[1..];
  assert |initial| == |points[..]|;
  forall k | 0 <= k < |points[..]|
    ensures points[..][k] == initial[k]
  {
    if k == 0 {
      assert points[..][k] == points[0];
      assert initial[k] == points[0];
    } else {
      assert 1 <= k < |points[..]|;
      assert initial[k] == points[1..][k - 1];
      assert points[1..][k - 1] == points[k];
      assert points[..][k] == points[k];
    }
  }
  assert forall k :: 0 <= k < |points[..]| ==> points[..][k] == initial[k];
  assert points[..] == initial;

  var i := 1;
  while i < n - 2
    invariant n == points.Length
    invariant 3 <= n
    invariant 1 <= i <= n - 2
    invariant 0 <= i <= points.Length
    invariant |[points[0]] + points[i..]| >= 3
    invariant area + polygon_area([points[0]] + points[i..]) == polygon_area(points[..])
    decreases n - 2 - i
  {
    var j := i + 1;
    assert i < n - 2;
    assert j <= n - 2;
    assert j < n;

    var (x1, y1) := points[0];
    var (x2, y2) := points[i];
    var (x3, y3) := points[j];
    var sign: real := x1 * (y2 - y3) + x2 * (y3 - y1) + x3 * (y1 - y2);
    var triangle_area := if sign < 0.0 then -sign / 2.0 else sign / 2.0;

    ghost var s := [points[0]] + points[i..];
    ghost var t := [points[0]] + points[j..];
    assert |s| >= 4;
    assert |s| != 3;
    assert |t| >= 3;
    assert s[0] == points[0];
    assert s[1] == points[i];
    assert s[2] == points[j];

    ghost var ss := s[2..];
    ghost var pp := points[j..];
    assert |ss| == |pp|;
    forall k | 0 <= k < |pp|
      ensures ss[k] == pp[k]
    {
      assert 0 <= k + 1 < |points[i..]|;
      assert ss[k] == s[k + 2];
      assert s[k + 2] == points[i..][k + 1];
      assert points[i..][k + 1] == points[i + k + 1];
      assert pp[k] == points[j + k];
      assert i + k + 1 == j + k;
    }
    assert forall k :: 0 <= k < |pp| ==> ss[k] == pp[k];
    assert ss == pp;
    assert s[2..] == points[j..];
    assert [s[0]] + s[2..] == t;
    assert |[s[0]] + s[2..]| == |t|;
    assert |[s[0]] + s[2..]| >= 3;

    if |s| == 3 {
      assert false;
    } else {
      ghost var (sx1, sy1) := s[0];
      ghost var (sx2, sy2) := s[1];
      ghost var (sx3, sy3) := s[2];
      ghost var signS: real := sx1 * (sy2 - sy3) + sx2 * (sy3 - sy1) + sx3 * (sy1 - sy2);
      ghost var triS: real := if signS < 0.0 then -signS / 2.0 else signS / 2.0;
      assert sx1 == x1 && sy1 == y1;
      assert sx2 == x2 && sy2 == y2;
      assert sx3 == x3 && sy3 == y3;
      assert signS == sign;
      assert triS == triangle_area;
      assert polygon_area(s) == triS + polygon_area([s[0]] + s[2..]);
      assert polygon_area([s[0]] + s[2..]) == polygon_area(t);
      assert polygon_area(s) == triangle_area + polygon_area(t);
    }
    assert area + triangle_area + polygon_area(t) == polygon_area(points[..]);

    area := area + triangle_area;
    i := j;
    assert [points[0]] + points[i..] == t;
    assert |[points[0]] + points[i..]| >= 3;
    assert area + polygon_area([points[0]] + points[i..]) == polygon_area(points[..]);
  }

  assert i == n - 2;
  ghost var s := [points[0]] + points[i..];
  assert |s| == 3;

  var (x1, y1) := points[0];
  var (x2, y2) := points[i];
  var (x3, y3) := points[i + 1];
  var sign: real := x1 * (y2 - y3) + x2 * (y3 - y1) + x3 * (y1 - y2);
  var last_area := if sign < 0.0 then -sign / 2.0 else sign / 2.0;

  assert s[0] == points[0];
  assert s[1] == points[i];
  assert s[2] == points[i + 1];
  ghost var (sx1, sy1) := s[0];
  ghost var (sx2, sy2) := s[1];
  ghost var (sx3, sy3) := s[2];
  ghost var signS: real := sx1 * (sy2 - sy3) + sx2 * (sy3 - sy1) + sx3 * (sy1 - sy2);
  ghost var triS: real := if signS < 0.0 then -signS / 2.0 else signS / 2.0;
  assert sx1 == x1 && sy1 == y1;
  assert sx2 == x2 && sy2 == y2;
  assert sx3 == x3 && sy3 == y3;
  assert signS == sign;
  assert triS == last_area;
  assert polygon_area(s) == triS;
  assert polygon_area(s) == last_area;
  assert area + last_area == polygon_area(points[..]);
  area := area + last_area;
  assert area == polygon_area(points[..]);
}