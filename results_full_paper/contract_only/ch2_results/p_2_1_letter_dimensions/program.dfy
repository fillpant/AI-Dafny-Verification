method p_2_1_letter_dimensions() returns (width: real, height: real)
	ensures width == 8.5 * 25.4
	ensures height == 11.0 * 25.4
{
  width := 8.5 * 25.4;
  height := 11.0 * 25.4;
}