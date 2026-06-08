method p_6_9_arrays_equal_array(first: array<int>, second: array<int>) returns (are_equal: bool)
	ensures are_equal == (first.Length == second.Length && forall i :: 0 <= i < first.Length ==> first[i] == second[i])
{
  if first.Length != second.Length {
    are_equal := false;
    assert !(first.Length == second.Length);
    assert !(first.Length == second.Length && (forall i :: 0 <= i < first.Length ==> first[i] == second[i]));
  } else {
    var i := 0;
    are_equal := true;
    while i < first.Length
      invariant first.Length == second.Length
      invariant 0 <= i <= first.Length
      invariant are_equal ==> (forall k :: 0 <= k < i ==> first[k] == second[k])
      invariant !are_equal ==> (exists k :: 0 <= k < i && first[k] != second[k])
      decreases first.Length - i
    {
      if first[i] != second[i] {
        are_equal := false;
        assert 0 <= i < i + 1 && first[i] != second[i];
        assert exists k :: 0 <= k < i + 1 && first[k] != second[k];
      } else {
        assert first[i] == second[i];
        if are_equal {
          assert forall k :: 0 <= k < i ==> first[k] == second[k];
          forall k | 0 <= k < i + 1
            ensures first[k] == second[k]
          {
            if k < i {
              assert first[k] == second[k];
            } else {
              assert k == i;
            }
          }
        } else {
          ghost var k :| 0 <= k < i && first[k] != second[k];
          assert 0 <= k < i + 1 && first[k] != second[k];
          assert exists j :: 0 <= j < i + 1 && first[j] != second[j];
        }
      }
      i := i + 1;
    }

    assert i == first.Length;
    if are_equal {
      assert forall k :: 0 <= k < first.Length ==> first[k] == second[k];
    } else {
      ghost var k :| 0 <= k < first.Length && first[k] != second[k];
      if forall j :: 0 <= j < first.Length ==> first[j] == second[j] {
        assert first[k] == second[k];
        assert false;
      }
      assert !(forall j :: 0 <= j < first.Length ==> first[j] == second[j]);
    }
  }
}