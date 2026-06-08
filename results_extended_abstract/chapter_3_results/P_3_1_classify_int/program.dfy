method P_3_1_classify_int (x:int) returns (s: string)
	ensures x == 0 ==> s == "zero"
	ensures x > 0 ==> s == "positive"
	ensures x < 0 ==> s == "negative"
{
  if x == 0 {
    s := "zero";
  } else if x > 0 {
    s := "positive";
  } else {
    s := "negative";
  }
}