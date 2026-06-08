method p4_3_b_every_second_letter(s: string) returns (result: string)
	ensures |result| * 2 == |s| || |result| * 2 + 1 == |s|
	ensures forall i :: 0 <= i < |result| ==> result[i] == s[2 * i]
{
  result := "";
  var i := 0;
  while i < |s|
    invariant 0 <= i <= |s| + 1
    invariant |result| * 2 == i || |result| * 2 + 1 == i
    invariant forall k :: 0 <= k < |result| ==> result[k] == s[2 * k]
  {
    result := result + s[i..i+1];
    i := i + 2;
  }
}