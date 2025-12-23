method p5_9_sphereSurface(r: real) returns (surface_area: real)
	ensures surface_area == 4.0 * 3.14159 * r * r
{
  surface_area := 4.0 * 3.14159 * r * r;
}