method p_4_9_reverse_string(s: string) returns (reversed: string)
	ensures |reversed| == |s|
	ensures forall i :: 0 <= i < |s| ==> reversed[i] == s[|s| - 1 - i]
{
  var n := |s|;
  reversed := "";
  var i := n;

  while i > 0
    invariant n == |s|
    invariant 0 <= i <= n
    invariant |reversed| == n - i
    invariant forall k :: 0 <= k < |reversed| ==> reversed[k] == s[n - 1 - k]
    decreases i
  {
    var oldReversed := reversed;
    var oldI := i;
    assert |oldReversed| == n - oldI;
    assert forall k :: 0 <= k < |oldReversed| ==> oldReversed[k] == s[n - 1 - k];

    i := i - 1;
    assert oldI == i + 1;
    assert 0 <= i < n;

    var piece := s[i..i+1];
    assert |piece| == 1;
    assert piece[0] == s[i];

    reversed := oldReversed + piece;
    assert |reversed| == |oldReversed| + |piece|;
    assert |reversed| == n - i;

    assert forall k :: 0 <= k < |reversed| ==> reversed[k] == s[n - 1 - k] by {
      forall k | 0 <= k < |reversed|
        ensures reversed[k] == s[n - 1 - k]
      {
        if k < |oldReversed| {
          assert reversed[k] == oldReversed[k];
          assert oldReversed[k] == s[n - 1 - k];
        } else {
          assert k >= |oldReversed|;
          assert k < |oldReversed| + |piece|;
          assert |piece| == 1;
          assert k == |oldReversed|;
          assert reversed[k] == piece[0];
          assert piece[0] == s[i];
          assert |oldReversed| == n - oldI;
          assert oldI == i + 1;
          assert |oldReversed| == n - (i + 1);
          assert k == n - (i + 1);
          assert n - 1 - k == i;
          assert reversed[k] == s[n - 1 - k];
        }
      }
    }
  }

  assert |reversed| == |s|;
  assert forall k :: 0 <= k < |s| ==> reversed[k] == s[|s| - 1 - k] by {
    forall k | 0 <= k < |s|
      ensures reversed[k] == s[|s| - 1 - k]
    {
      assert k < |reversed|;
      assert n == |s|;
      assert reversed[k] == s[n - 1 - k];
      assert n - 1 - k == |s| - 1 - k;
    }
  }
}