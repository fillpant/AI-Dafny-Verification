function mystring(s : string, n : nat): string
{
  if n == 0 then "" else s + mystring(s, n - 1)
}

method p_1_8() returns (s : string)
	ensures s == mystring("          !!!@@@@@@@@@@@@@@@@@@@@\n", 5)
{
  var line := "          !!!@@@@@@@@@@@@@@@@@@@@\n";
  s := line + line + line + line + line;
}