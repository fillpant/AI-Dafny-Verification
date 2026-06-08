method p4_8_seperate_lines(s: string) returns (chars: string)
	ensures |chars| == 2 * |s|
	ensures forall i :: 0 <= i < |s| ==> i % 2 == 1 ==> chars[i] == '\n'
	ensures forall i :: 0 <= i < |s| ==> i % 2 == 0 ==> chars[i] == s[i / 2]
{
  var res := "";
  var i := 0;
  while i < |s|
    invariant 0 <= i <= |s|
    invariant |res| == 2 * i
    invariant forall j :: 0 <= j < 2*i ==> j % 2 == 1 ==> res[j] == '\n'
    invariant forall k :: 0 <= k < i ==> res[2*k] == s[k]
  {
    res := res + s[i..i+1] + "\n";
    i := i + 1;
  }
  chars := res;
}