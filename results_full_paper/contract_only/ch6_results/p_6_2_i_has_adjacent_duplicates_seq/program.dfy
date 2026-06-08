method p_6_2_i_has_adjacent_duplicates_seq(inputs: seq<int>) returns (has_duplicates: bool)
	requires |inputs| >= 2
	ensures has_duplicates == (exists i :: 0 <= i < |inputs| - 1 && inputs[i] == inputs[i + 1])
{
  var i := 0;
  while i < |inputs| - 1
    invariant 0 <= i <= |inputs| - 1
    invariant forall j :: 0 <= j < i ==> inputs[j] != inputs[j + 1]
    decreases |inputs| - 1 - i
  {
    if inputs[i] == inputs[i + 1] {
      has_duplicates := true;
      assert 0 <= i < |inputs| - 1 && inputs[i] == inputs[i + 1];
      assert exists j :: 0 <= j < |inputs| - 1 && inputs[j] == inputs[j + 1];
      return;
    }

    assert inputs[i] != inputs[i + 1];
    var oldI := i;
    forall j | 0 <= j < oldI + 1
      ensures inputs[j] != inputs[j + 1]
    {
      if j < oldI {
        assert inputs[j] != inputs[j + 1];
      } else {
        assert j == oldI;
        assert inputs[j] != inputs[j + 1];
      }
    }
    i := i + 1;
  }

  assert i == |inputs| - 1;
  assert !(exists j :: 0 <= j < |inputs| - 1 && inputs[j] == inputs[j + 1]) by {
    if (exists k :: 0 <= k < |inputs| - 1 && inputs[k] == inputs[k + 1]) {
      var j :| 0 <= j < |inputs| - 1 && inputs[j] == inputs[j + 1];
      assert inputs[j] != inputs[j + 1];
      assert false;
    }
  }
  has_duplicates := false;
}