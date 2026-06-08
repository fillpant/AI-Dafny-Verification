method p_5_2_c_sorted(x: real, y: real, z: real) returns (is_sorted: bool)
	ensures is_sorted == (x <= y && y <= z)
{
  is_sorted := x <= y && y <= z;
}