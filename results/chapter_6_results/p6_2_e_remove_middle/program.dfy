method p6_2_e_remove_middle(arr: seq<int>) returns (result: seq<int>)
	requires |arr| >= 1
	ensures |result| == if |arr| % 2 == 1 then |arr| - 1 else |arr| - 2
	ensures |arr| % 2 == 1 ==> forall i :: 0 <= i < |arr| / 2 ==> result[i] == arr[i] && forall j :: |arr| / 2 <= j < |result| ==> result[j] == arr[j + 1]
	ensures |arr| % 2 == 0 ==> forall i :: 0 <= i < |arr| / 2 - 1 ==> result[i] == arr[i] && forall j :: |arr| / 2 - 1 <= j < |result| ==> result[j] == arr[j + 2]
{
  if |arr| % 2 == 1 {
    var mid := |arr| / 2;
    result := arr[..mid] + arr[mid+1..];
  } else {
    var mid1 := |arr| / 2 - 1;
    var mid2 := |arr| / 2;
    result := arr[..mid1] + arr[mid2+1..];
  }
}