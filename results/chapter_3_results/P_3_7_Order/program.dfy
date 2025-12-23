method P_3_7_Order (i:int, j: int, k: int) returns (s: string)
	ensures if (i < j < k) || (i > j > k) then s == "in order" else s == "not in order"
{
  if ((i < j && j < k) || (i > j && j > k)) {
    s := "in order";
  } else {
    s := "not in order";
  }
}