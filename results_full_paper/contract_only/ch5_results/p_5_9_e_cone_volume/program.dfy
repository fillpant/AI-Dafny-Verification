method p_5_9_e_cone_volume(r: real, h: real) returns (volume: real)
	ensures volume == (1.0 / 3.0) * 3.14159 * r * r * h
{
  volume := (1.0 / 3.0) * 3.14159 * r * r * h;
}