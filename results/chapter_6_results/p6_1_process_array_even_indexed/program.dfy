method p6_1_process_array_even_indexed(arr: seq<int>) returns (even_indexed: seq<int>)
	requires |arr| == 10
	ensures even_indexed == [arr[0], arr[2], arr[4], arr[6], arr[8]]
{
  even_indexed := [arr[0], arr[2], arr[4], arr[6], arr[8]];
}