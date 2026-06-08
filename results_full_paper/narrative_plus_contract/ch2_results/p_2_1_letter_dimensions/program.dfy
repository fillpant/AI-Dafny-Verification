method p_2_1_letter_dimensions() returns (width: real, height: real)
	ensures width == 8.5 * 25.4
	ensures height == 11.0 * 25.4
{
  // Conversion factor: one inch is exactly 25.4 millimeters.
  var millimetersPerInch: real := 25.4;

  // Letter-size paper dimensions in inches.
  var letterWidthInches: real := 8.5;
  var letterHeightInches: real := 11.0;

  // Convert the dimensions from inches to millimeters.
  width := letterWidthInches * millimetersPerInch;
  height := letterHeightInches * millimetersPerInch;
}