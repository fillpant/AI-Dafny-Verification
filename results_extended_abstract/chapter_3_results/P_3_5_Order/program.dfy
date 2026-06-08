method P_3_5_Order (i:int, j: int, k: int) returns (s: string)
	ensures if i < j < k then s == "increasing" else if i > j && j > k then s == "decreasing" else s== "neither"
{
  if i < j && j < k {
    s := "increasing";
  } else if i > j && j > k {
    s := "decreasing";
  } else {
    s := "neither";
  }
}