method p6_2_c_replace_even_with_zero(arr: seq<int>) returns (result: seq<int>)
	ensures |result| == |arr|
	ensures forall i :: 0 <= i < |arr| ==> (arr[i] % 2 == 0 ==> result[i] == 0) && (arr[i] % 2 != 0 ==> result[i] == arr[i])
{
  var res: seq<int> := [];
  var i := 0;
  while i < |arr|
    invariant 0 <= i <= |arr|
    invariant |res| == i
    invariant forall j :: 0 <= j < i ==> (arr[j] % 2 == 0 ==> res[j] == 0) && (arr[j] % 2 != 0 ==> res[j] == arr[j])
  {
    res := res + [if arr[i] % 2 == 0 then 0 else arr[i]];
    i := i + 1;
  }
  result := res;
}