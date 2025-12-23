method p_1_4() returns (first : real, second : real, third : real)
	ensures first == 1000.0 + 1000.0 * 0.05
	ensures second == first + first * 0.05
	ensures third == second + second * 0.05
{
  first := 1000.0 + 1000.0 * 0.05;
  second := first + first * 0.05;
  third := second + second * 0.05;
}