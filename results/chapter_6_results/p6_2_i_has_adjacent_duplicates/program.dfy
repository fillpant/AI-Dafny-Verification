function count_adajacent_duplicates(arr: seq<int>, i: int) : int
  requires 0 <= i < |arr| - 1
  decreases |arr| - i
{
  if i + 1 == |arr| - 1 then if arr[i] == arr[i + 1] then 1 else 0
  else if arr[i] == arr[i + 1] then 1 + count_adajacent_duplicates(arr, i + 1)
  else count_adajacent_duplicates(arr, i + 1)
} 

method p6_2_i_has_adjacent_duplicates(arr: seq<int>) returns (hasDuplicates: bool)
	requires |arr| >= 2
	ensures hasDuplicates == (exists i :: 0 <= i < |arr| - 1 && arr[i] == arr[i + 1])
	ensures 1 <= count_adajacent_duplicates(arr, 0) ==> hasDuplicates == true
{
  hasDuplicates := (exists i :: 0 <= i < |arr| - 1 && arr[i] == arr[i + 1]);
}