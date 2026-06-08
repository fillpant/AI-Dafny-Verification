method p6_1_process_array_reverse_order(arr: seq<int>) returns (reversed: seq<int>)
	requires |arr| == 10
	ensures |reversed| == |arr|
	ensures forall i :: 0 <= i < |reversed| ==> reversed[i] == arr[|arr| - 1 - i]
{
  var tmp := new int[|arr|];
  var j := 0;
  while j < |arr|
    invariant 0 <= j <= |arr|
    invariant forall k :: 0 <= k < j ==> tmp[k] == arr[|arr| - 1 - k]
  {
    tmp[j] := arr[|arr| - 1 - j];
    j := j + 1;
  }
  reversed := tmp[..];
}