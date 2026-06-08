method p_4_2_d_adjacent_duplicates_array_without_4th_ensures(inputs: array<int>) returns (duplicates: array<int>)
	ensures forall d :: d in duplicates[..] ==> d in inputs[..]
	ensures forall i :: 0 <= i < inputs.Length - 1 && inputs[i] == inputs[i + 1] ==> inputs[i] in duplicates[..]
	ensures forall d :: d in duplicates[..] ==> exists i :: 0 <= i < inputs.Length - 1 && inputs[i] == inputs[i + 1] && inputs[i] == d
{
  var acc: seq<int> := [];
  var i := 0;

  while i + 1 < inputs.Length
    invariant 0 <= i <= inputs.Length
    invariant forall j :: 0 <= j < i && j + 1 < inputs.Length && inputs[j] == inputs[j + 1] ==> inputs[j] in acc
    invariant forall d :: d in acc ==> exists j :: 0 <= j < i && j + 1 < inputs.Length && inputs[j] == inputs[j + 1] && inputs[j] == d
    decreases inputs.Length - i
  {
    var oldI := i;
    var nextI := i + 1;

    if inputs[oldI] == inputs[oldI + 1] {
      var oldAcc := acc;
      assert forall j :: 0 <= j < oldI && j + 1 < inputs.Length && inputs[j] == inputs[j + 1] ==> inputs[j] in oldAcc;
      assert forall d :: d in oldAcc ==> exists j :: 0 <= j < oldI && j + 1 < inputs.Length && inputs[j] == inputs[j + 1] && inputs[j] == d;

      acc := oldAcc + [inputs[oldI]];

      forall d | d in acc
        ensures exists j :: 0 <= j < nextI && j + 1 < inputs.Length && inputs[j] == inputs[j + 1] && inputs[j] == d
      {
        assert d in oldAcc + [inputs[oldI]];
        assert d in oldAcc || d in [inputs[oldI]];
        if d in oldAcc {
          var j :| 0 <= j < oldI && j + 1 < inputs.Length && inputs[j] == inputs[j + 1] && inputs[j] == d;
          assert 0 <= j < nextI;
          assert exists k :: 0 <= k < nextI && k + 1 < inputs.Length && inputs[k] == inputs[k + 1] && inputs[k] == d;
        } else {
          assert d in [inputs[oldI]];
          assert d == inputs[oldI];
          assert 0 <= oldI < nextI;
          assert oldI + 1 < inputs.Length;
          assert inputs[oldI] == inputs[oldI + 1];
          assert exists k :: 0 <= k < nextI && k + 1 < inputs.Length && inputs[k] == inputs[k + 1] && inputs[k] == d;
        }
      }

      forall j | 0 <= j < nextI && j + 1 < inputs.Length && inputs[j] == inputs[j + 1]
        ensures inputs[j] in acc
      {
        if j < oldI {
          assert inputs[j] in oldAcc;
          assert inputs[j] in acc;
        } else {
          assert j == oldI;
          assert inputs[j] == inputs[oldI];
          assert inputs[oldI] in [inputs[oldI]];
          assert inputs[oldI] in acc;
          assert inputs[j] in acc;
        }
      }
    } else {
      forall d | d in acc
        ensures exists j :: 0 <= j < nextI && j + 1 < inputs.Length && inputs[j] == inputs[j + 1] && inputs[j] == d
      {
        var j :| 0 <= j < oldI && j + 1 < inputs.Length && inputs[j] == inputs[j + 1] && inputs[j] == d;
        assert 0 <= j < nextI;
        assert exists k :: 0 <= k < nextI && k + 1 < inputs.Length && inputs[k] == inputs[k + 1] && inputs[k] == d;
      }

      forall j | 0 <= j < nextI && j + 1 < inputs.Length && inputs[j] == inputs[j + 1]
        ensures inputs[j] in acc
      {
        if j < oldI {
          assert inputs[j] in acc;
        } else {
          assert j == oldI;
          assert inputs[oldI] != inputs[oldI + 1];
          assert inputs[j] == inputs[j + 1];
          assert false;
        }
      }
    }

    i := nextI;
  }

  duplicates := new int[|acc|];
  var k := 0;
  while k < |acc|
    invariant 0 <= k <= |acc|
    invariant duplicates.Length == |acc|
    invariant forall t :: 0 <= t < k ==> duplicates[t] == acc[t]
    decreases |acc| - k
  {
    duplicates[k] := acc[k];
    k := k + 1;
  }

  assert duplicates.Length == |acc|;
  assert |duplicates[..]| == |acc|;
  forall t | 0 <= t < |acc|
    ensures duplicates[..][t] == acc[t]
  {
    assert duplicates[..][t] == duplicates[t];
    assert duplicates[t] == acc[t];
  }
  assert duplicates[..] == acc;

  assert !(i + 1 < inputs.Length);
  assert i + 1 >= inputs.Length;

  forall d | d in duplicates[..]
    ensures d in inputs[..]
  {
    assert d in acc;
    var j :| 0 <= j < i && j + 1 < inputs.Length && inputs[j] == inputs[j + 1] && inputs[j] == d;
    assert 0 <= j < inputs.Length;
    assert inputs[j] == d;
    assert inputs[j] in inputs[..];
  }

  forall j | 0 <= j < inputs.Length - 1 && inputs[j] == inputs[j + 1]
    ensures inputs[j] in duplicates[..]
  {
    assert j + 1 < inputs.Length;
    assert j + 1 < i + 1;
    assert j < i;
    assert inputs[j] in acc;
    assert inputs[j] in duplicates[..];
  }

  forall d | d in duplicates[..]
    ensures exists j :: 0 <= j < inputs.Length - 1 && inputs[j] == inputs[j + 1] && inputs[j] == d
  {
    assert d in acc;
    var j :| 0 <= j < i && j + 1 < inputs.Length && inputs[j] == inputs[j + 1] && inputs[j] == d;
    assert j < inputs.Length - 1;
    assert exists k :: 0 <= k < inputs.Length - 1 && inputs[k] == inputs[k + 1] && inputs[k] == d;
  }
}