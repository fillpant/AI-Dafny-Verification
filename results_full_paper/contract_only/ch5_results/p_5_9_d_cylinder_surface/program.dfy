method p_5_9_d_cylinder_surface(r: real, h: real) returns (surface: real)
	ensures surface == 2.0 * 3.14159 * r * h + 2.0 * 3.14159 * r * r
{
  surface := 2.0 * 3.14159 * r * h + 2.0 * 3.14159 * r * r;
}