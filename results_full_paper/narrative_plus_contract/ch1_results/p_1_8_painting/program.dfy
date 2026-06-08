function mystring(s: string, n: nat): string
{
  if n == 0 then "" else s + mystring(s, n - 1)
}

method p_1_8_painting() returns (s: string)
	ensures s == mystring("          !!!@@@@@@@@@@@@@@@@@@@@\n", 5)
{
  var line := "          !!!@@@@@@@@@@@@@@@@@@@@\n";
  s := line + (line + (line + (line + (line + ""))));

  assert mystring(line, 0) == "";
  assert mystring(line, 1) == line + mystring(line, 0);
  assert mystring(line, 1) == line + "";
  assert mystring(line, 2) == line + mystring(line, 1);
  assert mystring(line, 2) == line + (line + "");
  assert mystring(line, 3) == line + mystring(line, 2);
  assert mystring(line, 3) == line + (line + (line + ""));
  assert mystring(line, 4) == line + mystring(line, 3);
  assert mystring(line, 4) == line + (line + (line + (line + "")));
  assert mystring(line, 5) == line + mystring(line, 4);
  assert mystring(line, 5) == line + (line + (line + (line + (line + ""))));
}