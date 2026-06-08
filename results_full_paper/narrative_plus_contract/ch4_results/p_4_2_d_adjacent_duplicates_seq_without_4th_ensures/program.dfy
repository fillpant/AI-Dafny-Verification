method p_4_2_d_adjacent_duplicates_seq_without_4th_ensures(inputs: seq<int>) returns (duplicates: seq<int>)
	ensures forall d :: d in duplicates ==> d in inputs
	ensures forall i :: 0 <= i < |inputs| - 1 && inputs[i] == inputs[i + 1] ==> inputs[i] in duplicates
	ensures forall d :: d in duplicates ==> exists i :: 0 <= i < |inputs| - 1 && inputs[i] == inputs[i + 1] && inputs[i] == d
{
  duplicates := [];
  var i := 0;
  while i < |inputs| - 1
    invariant 0 <= i <= |inputs|
    invariant forall d :: d in duplicates ==> d in inputs
    invariant forall j :: 0 <= j < i && j < |inputs| - 1 && inputs[j] == inputs[j + 1] ==> inputs[j] in duplicates
    invariant forall d :: d in duplicates ==> exists j :: 0 <= j < i && j < |inputs| - 1 && inputs[j] == inputs[j + 1] && inputs[j] == d
    decreases |inputs| - i
  {
    var oldI := i;
    ghost var oldDuplicates := duplicates;

    assert forall d :: d in oldDuplicates ==> d in inputs;
    assert forall j :: 0 <= j < oldI && j < |inputs| - 1 && inputs[j] == inputs[j + 1] ==> inputs[j] in oldDuplicates;
    assert forall d :: d in oldDuplicates ==> exists j :: 0 <= j < oldI && j < |inputs| - 1 && inputs[j] == inputs[j + 1] && inputs[j] == d;

    if inputs[i] == inputs[i + 1] {
      if !(inputs[i] in duplicates) {
        assert 0 <= i < |inputs|;
        assert inputs[i] in inputs;
        duplicates := duplicates + [inputs[i]];
        assert duplicates == oldDuplicates + [inputs[oldI]];
        assert inputs[oldI] in duplicates;
      } else {
        assert inputs[oldI] in duplicates;
      }
    }

    assert duplicates == oldDuplicates || duplicates == oldDuplicates + [inputs[oldI]];
    assert duplicates != oldDuplicates ==> duplicates == oldDuplicates + [inputs[oldI]];
    assert duplicates != oldDuplicates ==> inputs[oldI] == inputs[oldI + 1];
    assert inputs[oldI] == inputs[oldI + 1] ==> inputs[oldI] in duplicates;

    forall d | d in oldDuplicates
      ensures d in duplicates
    {
      if duplicates != oldDuplicates {
        assert duplicates == oldDuplicates + [inputs[oldI]];
        assert d in oldDuplicates + [inputs[oldI]];
      }
    }

    forall d | d in duplicates
      ensures d in inputs
    {
      if d in oldDuplicates {
        assert d in inputs;
      } else {
        assert duplicates != oldDuplicates;
        assert duplicates == oldDuplicates + [inputs[oldI]];
        assert d in oldDuplicates + [inputs[oldI]];
        assert d in [inputs[oldI]];
        assert d == inputs[oldI];
        assert 0 <= oldI < |inputs|;
        assert inputs[oldI] in inputs;
      }
    }

    i := i + 1;
    assert i == oldI + 1;

    forall j | 0 <= j < i && j < |inputs| - 1 && inputs[j] == inputs[j + 1]
      ensures inputs[j] in duplicates
    {
      if j < oldI {
        assert inputs[j] in oldDuplicates;
        assert inputs[j] in duplicates;
      } else {
        assert oldI <= j;
        assert j < oldI + 1;
        assert j == oldI;
        assert inputs[oldI] == inputs[oldI + 1];
        assert inputs[oldI] in duplicates;
      }
    }

    forall d | d in duplicates
      ensures exists j :: 0 <= j < i && j < |inputs| - 1 && inputs[j] == inputs[j + 1] && inputs[j] == d
    {
      if d in oldDuplicates {
        assert exists j :: 0 <= j < oldI && j < |inputs| - 1 && inputs[j] == inputs[j + 1] && inputs[j] == d;
        ghost var k :| 0 <= k < oldI && k < |inputs| - 1 && inputs[k] == inputs[k + 1] && inputs[k] == d;
        assert 0 <= k < i;
        assert k < |inputs| - 1;
        assert inputs[k] == inputs[k + 1];
        assert inputs[k] == d;
      } else {
        assert duplicates != oldDuplicates;
        assert duplicates == oldDuplicates + [inputs[oldI]];
        assert d in oldDuplicates + [inputs[oldI]];
        assert d in [inputs[oldI]];
        assert d == inputs[oldI];
        assert inputs[oldI] == inputs[oldI + 1];
        assert 0 <= oldI < i;
        assert oldI < |inputs| - 1;
      }
    }
  }

  forall j | 0 <= j < |inputs| - 1 && inputs[j] == inputs[j + 1]
    ensures inputs[j] in duplicates
  {
    assert !(i < |inputs| - 1);
    assert j < i;
  }
}