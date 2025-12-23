method letter_perimeter() returns (perimeter:real, diagonal:real)
	ensures perimeter == (8.5 * 25.4) * 2.0 + 11.0 * 25.4 * 2.0
	ensures diagonal * diagonal == (8.5 * 25.4) * (8.5 * 25.4) + 11.0 * 25.4 * 11.0 * 25.4
{
  var width: real := 8.5 * 25.4;
  var height: real := 11.0 * 25.4;

  perimeter := width * 2.0 + height * 2.0;

  var diagSquared: real := width * width + height * height;
  diagonal :| (diagonal * diagonal == diagSquared);
}