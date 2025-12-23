method letter_dimensions() returns (width:real, height:real)
	ensures width == 8.5 * 25.4
	ensures height == 11.0 * 25.4
{
  // millimeters per inch
  var INCH_MM := 25.4;
  // letter size in inches
  var WIDTH_IN := 8.5;
  var HEIGHT_IN := 11.0;
  // compute dimensions in millimeters
  width := WIDTH_IN * INCH_MM;
  height := HEIGHT_IN * INCH_MM;
}