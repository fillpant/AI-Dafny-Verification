method p5_9_coneSurface(r: real, h: real) returns (surface_area: real)
	ensures (-r + (surface_area / (3.14159 * r))) * (-r + (surface_area / (3.14159 * r))) == h * h + r * r
{
  if r == 0.0 {
    assert false;
  }
  {:trigger slant * slant}
  var slant :| slant * slant == h * h + r * r;
  surface_area := 3.14159 * r * (r + slant);
}