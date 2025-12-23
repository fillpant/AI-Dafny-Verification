method P_3_2_classify_real (x:real) returns (s: string)
	ensures x == 0.0 ==> s == "zero, small"
	ensures 1.0 > x > 0.0 ==> s == "positive, small"
	ensures 1.0 <= x < 1000000.0 ==> s == "positive"
	ensures 1000000.0 <= x  ==> s == "positive, large"
	ensures 0.0 > x > -1.0 ==> s == "negative, small"
	ensures -1.0 >= x > -1000000.0 ==> s == "negative"
	ensures -1000000.0 >= x ==> s == "negative, large"
{
  if x == 0.0 {
    s := "zero, small";
  } else if x > 0.0 {
    if x < 1.0 {
      s := "positive, small";
    } else if x < 1000000.0 {
      s := "positive";
    } else {
      s := "positive, large";
    }
  } else {
    if x > -1.0 {
      s := "negative, small";
    } else if x > -1000000.0 {
      s := "negative";
    } else {
      s := "negative, large";
    }
  }
}