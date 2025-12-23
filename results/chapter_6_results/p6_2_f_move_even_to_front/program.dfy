method p6_2_f_move_even_to_front(arr: seq<int>) returns (result: seq<int>)
	ensures |result| == |arr|
	ensures forall i, j :: 0 <= i < j < |result| && result[i] % 2 == 0 && result[j] % 2 != 0
	ensures forall i :: 0 <= i < |arr| ==> exists j :: 0 <= j < |result| && arr[i] == result[j]
{
  result := [];

  var i := 0;
  while i < |arr|
    invariant 0 <= i <= |arr|
    invariant |result| <= |arr|
    invariant forall k :: 0 <= k < i && arr[k] % 2 == 0 ==> exists j :: 0 <= j < |result| && result[j] == arr[k]
    invariant forall j :: 0 <= j < |result| ==> result[j] % 2 == 0
  {
    if arr[i] % 2 == 0 {
      result := result + [arr[i]];
    }
    i := i + 1;
  }

  i := 0;
  while i < |arr|
    invariant 0 <= i <= |arr|
    invariant |result| <= |arr|
    invariant forall k :: 0 <= k < |arr| && arr[k] % 2 == 0 ==> exists j :: 0 <= j < |result| && result[j] == arr[k]
    invariant forall k :: 0 <= k < i && arr[k] % 2 != 0 ==> exists j :: 0 <= j < |result| && result[j] == arr[k]
    invariant forall j :: 0 <= j < |result| ==> (result[j] % 2 == 0 || (exists k :: 0 <= k < i && arr[k] == result[j]))
  {
    if arr[i] % 2 != 0 {
      result := result + [arr[i]];
    }
    i := i + 1;
  }
}