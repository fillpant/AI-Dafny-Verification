method p6_2_a_swap_first_last(arr: seq<int>) returns (result: seq<int>)
	requires |arr| >= 2
	ensures |result| == |arr|
	ensures result[0] == arr[|arr| - 1]
	ensures result[|arr| - 1] == arr[0]
	ensures forall i :: 1 <= i < |arr| - 1 ==> result[i] == arr[i]
{
  result := [arr[|arr| - 1]] + arr[1..|arr| - 1] + [arr[0]];
}