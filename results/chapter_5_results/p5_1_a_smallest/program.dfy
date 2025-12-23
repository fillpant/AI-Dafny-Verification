method p5_1_a_smallest(x: real, y: real, z: real) returns (smallest: real)
	ensures smallest <= x && smallest <= y && smallest <= z
	ensures smallest == x || smallest == y || smallest == z
{
  var s := x;
  if y < s {
    s := y;
  }
  if z < s {
    s := z;
  }
  smallest := s;
}