method p_6_9_arrays_equal_array(first: array<int>, second: array<int>) returns (are_equal: bool)
	ensures are_equal == (first.Length == second.Length && forall i :: 0 <= i < first.Length ==> first[i] == second[i])
{
  if first.Length != second.Length {
    are_equal := false;
    assert first.Length != second.Length;
    return;
  }

  var i := 0;
  while i < first.Length
    invariant 0 <= i <= first.Length
    invariant first.Length == second.Length
    invariant forall j :: 0 <= j < i ==> first[j] == second[j]
  {
    if first[i] != second[i] {
      are_equal := false;
      assert 0 <= i < first.Length;
      assert first[i] != second[i];
      assert !(forall j :: 0 <= j < first.Length ==> first[j] == second[j]) by {
        if forall j :: 0 <= j < first.Length ==> first[j] == second[j] {
          assert first[i] == second[i];
          assert false;
        }
      }
      return;
    }

    assert first[i] == second[i];
    forall j | 0 <= j < i + 1
      ensures first[j] == second[j]
    {
      if j < i {
        assert first[j] == second[j];
      } else {
        assert j == i;
        assert first[j] == second[j];
      }
    }
    assert forall j :: 0 <= j < i + 1 ==> first[j] == second[j];
    i := i + 1;
  }

  assert i == first.Length;
  forall j | 0 <= j < first.Length
    ensures first[j] == second[j]
  {
    assert 0 <= j < i;
    assert first[j] == second[j];
  }
  assert forall j :: 0 <= j < first.Length ==> first[j] == second[j];
  are_equal := true;
}