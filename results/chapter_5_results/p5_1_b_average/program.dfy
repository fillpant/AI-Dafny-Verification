method p5_1_b_average(x: real, y: real, z: real) returns (average: real)
	ensures average == (x + y + z) / 3.0
{
  average := (x + y + z) / 3.0;
}