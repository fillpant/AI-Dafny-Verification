method p_2_2_letter_perimeter() returns (perimeter: real, diagonal: real)
	ensures perimeter == (8.5 + 11.0) * 2.0
	ensures -0.01 < (diagonal * diagonal) - ((8.5 * 8.5) + (11.0 * 11.0)) < 0.01
{
  perimeter := (8.5 + 11.0) * 2.0;
  diagonal := 13.9014;

  assert diagonal * diagonal == 193.24892196;
  assert (8.5 * 8.5) + (11.0 * 11.0) == 193.25;
  assert (diagonal * diagonal) - ((8.5 * 8.5) + (11.0 * 11.0)) == -0.00107804;
  assert -0.01 < -0.00107804;
  assert -0.00107804 < 0.01;
}