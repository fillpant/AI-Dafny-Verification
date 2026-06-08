method rectangle_properties(length: real, width: real) returns (area: real, perimeter: real, diagonal: real)
	ensures area == length * width
	ensures perimeter == 2.0 * (length + width)
	ensures diagonal * diagonal == length * length + width * width
{
  area := length * width;
  perimeter := 2.0 * (length + width);
  diagonal {:trigger diagonal * diagonal} :| diagonal * diagonal == length * length + width * width;
}