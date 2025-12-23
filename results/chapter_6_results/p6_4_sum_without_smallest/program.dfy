function find_smallest(arr: seq<int>) : (ret : int)
  requires |arr| >= 1
  ensures forall x :: x in arr ==> ret <= x 
{
  if |arr| == 1 then arr[0]
  else 
    assert 2 <= |arr|;
    var rest_smallest := find_smallest(arr[1..]);
    var ret : int := if arr[0] <= rest_smallest then arr[0] else rest_smallest;
    assert arr == [arr[0]] + arr[1..]; 
    assert ret == if arr[0] <= rest_smallest then arr[0] else rest_smallest;
    ret 
}

function sum_array(arr: seq<int>) : int
{
  if |arr| == 0 then 0
  else  arr[0] + sum_array(arr[1..])
}

method p6_4_sum_without_smallest(arr: seq<int>) returns (sum: int)
	requires |arr| >= 1
	ensures sum == sum_array(arr) - find_smallest(arr)
{
  var runningSum := 0;
  var smallest := arr[0];
  var i := 0;
  while i < |arr|
    invariant 0 <= i <= |arr|
    invariant runningSum == sum_array(arr[..i])
    invariant i == 0 || smallest == find_smallest(arr[..i])
  {
    runningSum := runningSum + arr[i];
    if i == 0 || arr[i] < smallest {
      smallest := arr[i];
    }
    i := i + 1;
  }
  sum := runningSum - smallest;
}