method p_4_9_reverse_string(s: string) returns (reversed: string)
	ensures |reversed| == |s|
	ensures forall i :: 0 <= i < |s| ==> reversed[i] == s[|s| - 1 - i]
{
  reversed := "";
  var i := 0;
  while i < |s|
    invariant 0 <= i <= |s|
    invariant |reversed| == i
    invariant forall j :: 0 <= j < i ==> reversed[j] == s[|s| - 1 - j]
  {
    ghost var oldI := i;
    ghost var oldReversed := reversed;
    assert oldI < |s|;
    assert |oldReversed| == oldI;
    assert forall j :: 0 <= j < oldI ==> oldReversed[j] == s[|s| - 1 - j];

    reversed := reversed + [s[|s| - 1 - i]];
    assert reversed == oldReversed + [s[|s| - 1 - oldI]];
    i := i + 1;
    assert i == oldI + 1;
    assert |reversed| == i;

    forall j | 0 <= j < i
      ensures reversed[j] == s[|s| - 1 - j]
    {
      if j < oldI {
        assert oldReversed[j] == s[|s| - 1 - j];
        assert reversed[j] == oldReversed[j];
      } else {
        assert j == oldI;
        assert reversed[j] == s[|s| - 1 - oldI];
        assert |s| - 1 - oldI == |s| - 1 - j;
      }
    }
  }
  assert i == |s|;
  assert forall j :: 0 <= j < |s| ==> reversed[j] == s[|s| - 1 - j];
}