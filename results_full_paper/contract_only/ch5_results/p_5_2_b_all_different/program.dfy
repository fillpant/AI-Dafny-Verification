method p_5_2_b_all_different(x: real, y: real, z: real) returns (all_diff: bool)
	ensures all_diff == (x != y && y != z && x != z)
{
  all_diff := x != y && y != z && x != z;
}