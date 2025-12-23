method p6_7_reverse_array(arr: seq<int>) returns (reversed: seq<int>)
	ensures |reversed| == |arr|
	ensures forall i :: 0 <= i < |reversed| ==> reversed[i] == arr[|arr| - 1 - i]
{
  var r := [];
  var i := |arr|;
  while i > 0
    invariant 0 <= i <= |arr|
    invariant |r| == |arr| - i
    invariant forall k :: 0 <= k < |r| ==> r[k] == arr[|arr| - 1 - k]
  {
    i := i - 1;
    r := r + [arr[i]];
  }
  reversed := r;
}