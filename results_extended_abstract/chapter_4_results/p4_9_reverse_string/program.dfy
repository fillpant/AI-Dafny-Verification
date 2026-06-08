method p4_9_reverse_string(s: string) returns (reversed: string)
	ensures |reversed| == |s|
	ensures forall i :: 0 <= i < |s| ==> reversed[i] == s[|s| - 1 - i]
{
  var r := "";
  var i := |s|;
  while i > 0
    invariant 0 <= i <= |s|
    invariant |r| == |s| - i
    invariant forall k :: 0 <= k < |r| ==> r[k] == s[|s| - 1 - k]
  {
    i := i - 1;
    r := r + s[i .. i+1];
  }
  reversed := r;
}