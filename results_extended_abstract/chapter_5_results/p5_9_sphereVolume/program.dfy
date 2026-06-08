method p5_9_sphereVolume(r: real) returns (volume: real)
	ensures volume == (4.0 / 3.0) * 3.14159 * r * r * r
{
  volume := (4.0 / 3.0) * 3.14159 * r * r * r;
}