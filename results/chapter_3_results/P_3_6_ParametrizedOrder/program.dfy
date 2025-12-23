method P_3_6_ParametrizedOrder (i:int, j: int, k: int, strict: bool ) returns (s: string)
	ensures if strict then if i < j < k then s == "increasing" else if i > j && j > k then s == "decreasing" else s == "neither" else if i <= j <= k then if i == j == k then s == "increasing and decreasing" else s == "increasing" else if i >= j && j >= k then s == "decreasing" else s == "neither"
{
  if strict {
    if i < j && j < k {
      s := "increasing";
    } else if i > j && j > k {
      s := "decreasing";
    } else {
      s := "neither";
    }
  } else {
    if i <= j && j <= k {
      if i == j && j == k {
        s := "increasing and decreasing";
      } else {
        s := "increasing";
      }
    } else if i >= j && j >= k {
      s := "decreasing";
    } else {
      s := "neither";
    }
  }
}