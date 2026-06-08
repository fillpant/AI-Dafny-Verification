method p_13_1_recursive_rectangle_area(width: nat, height: nat) returns (area: nat)
	requires 1 <= width
	requires 1 <= height
	ensures area == width * height
{
  if height == 1 {
    area := width;
  } else {
    var smallerArea := p_13_1_recursive_rectangle_area(width, height - 1);
    area := smallerArea + width;
  }
}