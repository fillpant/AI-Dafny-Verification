function find_largest(arr: seq<int>) : (ret : int)
  requires |arr| >= 1
  ensures forall x :: x in arr ==> x <= ret
{
  if |arr| == 1 then arr[0]
  else 
    assert 2 <= |arr|;
    var rest_largest := find_largest(arr[1..]);
    var ret : int := if arr[0] >= rest_largest then arr[0] else rest_largest;
    assert arr == [arr[0]] + arr[1..]; 
    ret 
} 

method p6_2_g_second_largest(arr: seq<int>) returns (second_largest: int)
	requires |arr| >= 2
	ensures second_largest < find_largest(arr)
	ensures forall x :: x in arr ==> x < find_largest(arr) ==> x <= second_largest
{
  // First pass: find largest
  var largest := arr[0];
  var i := 1;
  while i < |arr|
    invariant 1 <= i <= |arr|
    invariant forall j :: 0 <= j < i ==> arr[j] <= largest
  {
    if arr[i] > largest {
      largest := arr[i];
    }
    i := i + 1;
  }

  // Second pass: find the maximum element strictly less than largest
  var found := false;
  var second := 0;  // dummy initial value, replaced once found == true
  var j := 0;
  while j < |arr|
    invariant 0 <= j <= |arr|
    invariant !found ==> forall k :: 0 <= k < j ==> arr[k] == largest
    invariant found ==> second < largest
    invariant found ==> forall k :: 0 <= k < j ==> (arr[k] < largest ==> arr[k] <= second)
  {
    if arr[j] < largest {
      if !found {
        second := arr[j];
        found := true;
      } else if arr[j] > second {
        second := arr[j];
      }
    }
    j := j + 1;
  }

  // found must be true because |arr| >= 2 and not all elements can exceed largest
  second_largest := second;
}