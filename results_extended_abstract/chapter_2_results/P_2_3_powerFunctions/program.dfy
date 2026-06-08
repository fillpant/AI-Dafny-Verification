method power_functions(x: int) returns (sq: int, cube : int, fourth: int)
	ensures sq == x * x
	ensures cube == x * x * x
	ensures fourth == x * x * x * x
{
  sq := x * x;
  cube := x * x * x;
  fourth := x * x * x * x;
}