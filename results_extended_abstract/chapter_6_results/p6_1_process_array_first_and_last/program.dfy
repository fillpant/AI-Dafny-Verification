method p6_1_process_array_first_and_last(arr: seq<int>) returns (first_and_last: seq<int>)
	requires |arr| == 10
	ensures first_and_last == [arr[0], arr[|arr| - 1]]
{
  first_and_last := [arr[0], arr[|arr| - 1]];
}