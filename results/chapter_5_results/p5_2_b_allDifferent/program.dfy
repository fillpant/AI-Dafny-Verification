method p5_2_b_allDifferent(x: real, y: real, z: real) returns (allDiff: bool)
	ensures allDiff == (x != y && y != z && x != z)
{
  allDiff := x != y && y != z && x != z;
}