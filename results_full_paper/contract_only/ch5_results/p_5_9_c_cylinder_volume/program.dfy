method p_5_9_c_cylinder_volume(r: real, h: real) returns (volume: real)
	ensures volume == 3.14159 * r * r * h
{
  volume := 3.14159 * r * r * h;
}