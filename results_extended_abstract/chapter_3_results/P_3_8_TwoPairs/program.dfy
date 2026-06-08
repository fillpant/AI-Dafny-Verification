method P_3_8_TwoPairs (i:int, j: int, k: int, l: int) returns (s: string)
	ensures if (i==j && k==l) || (i==k && j==l) || (i==l && j==k) then s == "two pairs" else s == "not two pairs"
{
  if ((i == j && k == l) || (i == k && j == l) || (i == l && j == k)) {
    s := "two pairs";
  } else {
    s := "not two pairs";
  }
}