method p_13_2_recursive_square_area(width: nat) returns (area: nat)
	requires 1 <= width
	ensures area == width * width
{
  if width == 1 {
    area := 1;
  } else {
    var smallerArea := p_13_2_recursive_square_area(width - 1);
    area := width * width;
  }
}