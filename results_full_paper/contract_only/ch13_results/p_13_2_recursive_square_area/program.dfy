method p_13_2_recursive_square_area(width: nat) returns (area: nat)
	requires 1 <= width
	ensures area == width * width
{
  area := width * width;
}