method average(x: int, y: int) returns (result:real)
	ensures result == (x + y) as real / 2.0
{
  result := (x + y) as real / 2.0;
}