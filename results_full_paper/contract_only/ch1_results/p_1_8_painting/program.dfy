function mystring(s: string, n: nat): string
{
  if n == 0 then "" else s + mystring(s, n - 1)
}

method p_1_8_painting() returns (s: string)
	ensures s == mystring("          !!!@@@@@@@@@@@@@@@@@@@@\n", 5)
{
  s := "          !!!@@@@@@@@@@@@@@@@@@@@\n" +
       ("          !!!@@@@@@@@@@@@@@@@@@@@\n" +
       ("          !!!@@@@@@@@@@@@@@@@@@@@\n" +
       ("          !!!@@@@@@@@@@@@@@@@@@@@\n" +
       ("          !!!@@@@@@@@@@@@@@@@@@@@\n" + ""))));
}