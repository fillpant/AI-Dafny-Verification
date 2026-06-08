method p_5_2_a_all_the_same(x: real, y: real, z: real) returns (all_same: bool)
	ensures all_same == (x == y && y == z)
{
  all_same := x == y && y == z;
}