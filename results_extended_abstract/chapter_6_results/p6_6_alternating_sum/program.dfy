function sum_arrray(arr : seq<int>, i : int) : int
{
  if |arr| == 0 then 0
  else arr[0] * i + sum_arrray(arr[1..], i * -1)
}

method p6_6_alternating_sum(arr: seq<int>) returns (alt_sum: int)
	ensures alt_sum == sum_arrray(arr, 1)
{
  alt_sum := 0;
  var i := 0;
  while i < |arr|
    invariant 0 <= i <= |arr|
    invariant alt_sum + sum_arrray(arr[i..], if i % 2 == 0 then 1 else -1) == sum_arrray(arr, 1)
  {
    var sign := if i % 2 == 0 then 1 else -1;
    alt_sum := alt_sum + arr[i] * sign;
    i := i + 1;
  }
}