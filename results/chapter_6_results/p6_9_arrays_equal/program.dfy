method p6_9_arrays_equal(arr1: seq<int>, arr2: seq<int>) returns (areEqual: bool)
	ensures areEqual == (|arr1| == |arr2| && forall i :: 0 <= i < |arr1| ==> arr1[i] == arr2[i])
{
  if |arr1| != |arr2| {
    areEqual := false;
  } else {
    areEqual := (forall i :: 0 <= i < |arr1| ==> arr1[i] == arr2[i]);
  }
}