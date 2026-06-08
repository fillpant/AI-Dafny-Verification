method min(x: int, y: int) returns (result:int)
	ensures result == x || result == y
	ensures if x <= y then result == x else result == y
{
  if x <= y {
    result := x;
  } else {
    result := y;
  }
}