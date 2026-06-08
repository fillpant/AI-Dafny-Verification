method p5_9_cylinderSurface(r: real, h: real) returns (surface_area: real)
	ensures surface_area == 2.0 * 3.14159 * r * (r + h)
{
  surface_area := 2.0 * 3.14159 * r * (r + h);
}