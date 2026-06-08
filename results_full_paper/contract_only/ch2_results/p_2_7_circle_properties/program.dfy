method p_2_7_circle_properties(radius: real) returns (circumference: real, area: real, volume: real, surface_area: real)
	ensures circumference == 2.0 * 3.14159 * radius
	ensures area == 3.14159 * radius * radius
	ensures volume == (4.0 / 3.0) * 3.14159 * radius * radius * radius
	ensures surface_area == 4.0 * 3.14159 * radius * radius
{
  circumference := 2.0 * 3.14159 * radius;
  area := 3.14159 * radius * radius;
  volume := (4.0 / 3.0) * 3.14159 * radius * radius * radius;
  surface_area := 4.0 * 3.14159 * radius * radius;
}