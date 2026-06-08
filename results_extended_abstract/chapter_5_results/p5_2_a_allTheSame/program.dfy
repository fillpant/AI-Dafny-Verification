method p5_2_a_allTheSame(x: real, y: real, z: real) returns (allSame: bool)
	ensures allSame == (x == y && y == z)
{
  allSame := x == y && y == z;
}