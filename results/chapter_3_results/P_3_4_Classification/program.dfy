method P_3_4_Classification (i:int, j: int, k: int) returns (s: string)
	ensures if i == j == k then s == "all the same" else if i != j && j!=k && i!=k then s == "all different" else s== "neither"
{
  if i == j && j == k {
    s := "all the same";
  } else if i != j && j != k && i != k {
    s := "all different";
  } else {
    s := "neither";
  }
}