method p5_9_cylinderVolume(r: real, h: real) returns (volume: real)
	ensures volume == 3.14159 * r * r * h
{
  volume := 3.14159 * r * r * h;
}