method p6_2_b_shift_right(arr: seq<int>) returns (result: seq<int>)
	requires |arr| >= 1
	ensures |result| == |arr|
	ensures result[0] == arr[|arr| - 1]
	ensures forall i :: 1 <= i < |arr| ==> result[i] == arr[i - 1]
{
  var n := |arr|;
  result := arr[n - 1 .. n] + arr[0 .. n - 1];
}