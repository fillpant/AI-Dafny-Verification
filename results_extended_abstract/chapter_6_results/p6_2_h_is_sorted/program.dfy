method p6_2_h_is_sorted(arr: seq<int>) returns (isSorted: bool)
	ensures isSorted == (forall i :: 0 <= i < |arr| - 1 ==> arr[i] <= arr[i + 1])
{
  isSorted := true;
  var i := 0;
  while i < |arr| - 1
    invariant 0 <= i <= |arr| - 1
    invariant isSorted ==> (forall j :: 0 <= j < i ==> arr[j] <= arr[j + 1])
  {
    if arr[i] > arr[i + 1] {
      isSorted := false;
      break;
    }
    i := i + 1;
  }
}