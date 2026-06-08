method p_13_1_recursive_rectangle_area(width: nat, height: nat) returns (area: nat)
	requires 1 <= width
	requires 1 <= height
	ensures area == width * height
{
  if width == 1 {
    area := height;
  } else {
    var smallerArea := p_13_1_recursive_rectangle_area(width - 1, height);
    area := smallerArea + height;
  }
}