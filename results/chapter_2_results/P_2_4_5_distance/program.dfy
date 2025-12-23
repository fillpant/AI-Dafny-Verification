method distance(x: int, y: int) returns (result:int)
	ensures result >= 0
	ensures if x >= y then result == x - y else result == y - x
{
  if x >= y {
    result := x - y;
  } else {
    result := y - x;
  }
}