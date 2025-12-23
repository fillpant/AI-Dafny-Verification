method p6_2_d_replace_with_larger_neighbor(arr: seq<int>) returns (result: seq<int>)
	requires |arr| >= 3
	ensures |result| == |arr|
	ensures result[0] == arr[0]
	ensures result[|arr| - 1] == arr[|arr| - 1]
	ensures forall i :: 1 <= i < |arr| - 1 ==> result[i] == if arr[i - 1] >= arr[i + 1] then arr[i - 1] else arr[i + 1]
{
  var s := [arr[0]];
  var i := 1;
  while i < |arr| - 1
    invariant 1 <= i <= |arr| - 1
    invariant |s| == i
    invariant s[0] == arr[0]
    invariant forall k :: 1 <= k < i ==> s[k] == (if arr[k - 1] >= arr[k + 1] then arr[k - 1] else arr[k + 1])
  {
    s := s + [if arr[i - 1] >= arr[i + 1] then arr[i - 1] else arr[i + 1]];
    i := i + 1;
  }
  s := s + [arr[|arr| - 1]];
  result := s;
}