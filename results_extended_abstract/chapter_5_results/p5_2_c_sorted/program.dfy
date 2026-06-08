method p5_2_c_sorted(x: real, y: real, z: real) returns (isSorted: bool)
	ensures isSorted == (x <= y && y <= z)
{
  isSorted := x <= y && y <= z;
}