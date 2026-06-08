method p6_2_j_has_duplicates(arr: seq<int>) returns (hasDuplicates: bool)
	requires |arr| >= 2
	ensures hasDuplicates == (exists i, j :: 0 <= i < j < |arr| && arr[i] == arr[j])
{
  var seen: set<int> := {};
  var i := 0;
  while i < |arr|
    invariant 0 <= i <= |arr|
    invariant seen == set x | 0 <= x < i :: arr[x]
    invariant |seen| == i
    invariant forall a, b :: 0 <= a < b < i ==> arr[a] != arr[b]
  {
    if arr[i] in seen {
      return true;
    }
    seen := seen + {arr[i]};
    i := i + 1;
  }
  return false;
}