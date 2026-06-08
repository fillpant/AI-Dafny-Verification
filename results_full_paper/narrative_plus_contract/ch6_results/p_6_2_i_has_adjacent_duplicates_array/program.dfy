method p_6_2_i_has_adjacent_duplicates_array(inputs: array<int>) returns (has_duplicates: bool)
	requires inputs.Length >= 2
	ensures has_duplicates == (exists i :: 0 <= i < inputs.Length - 1 && inputs[i] == inputs[i + 1])
{
  var i := 0;

  while i < inputs.Length - 1
    invariant 0 <= i <= inputs.Length - 1
    invariant forall j :: 0 <= j < i ==> inputs[j] != inputs[j + 1]
    decreases inputs.Length - 1 - i
  {
    if inputs[i] == inputs[i + 1] {
      has_duplicates := true;
      assert 0 <= i < inputs.Length - 1;
      assert inputs[i] == inputs[i + 1];
      assert exists j :: 0 <= j < inputs.Length - 1 && inputs[j] == inputs[j + 1];
      return;
    } else {
      assert inputs[i] != inputs[i + 1];
      forall j | 0 <= j < i + 1
        ensures inputs[j] != inputs[j + 1]
      {
        if j < i {
          assert inputs[j] != inputs[j + 1];
        } else {
          assert j == i;
          assert inputs[j] != inputs[j + 1];
        }
      }
      i := i + 1;
    }
  }

  has_duplicates := false;
  assert i == inputs.Length - 1;

  forall j | 0 <= j < inputs.Length - 1
    ensures inputs[j] != inputs[j + 1]
  {
    assert j < i;
    assert inputs[j] != inputs[j + 1];
  }

  if (exists j :: 0 <= j < inputs.Length - 1 && inputs[j] == inputs[j + 1]) {
    var k :| 0 <= k < inputs.Length - 1 && inputs[k] == inputs[k + 1];
    assert inputs[k] != inputs[k + 1];
    assert false;
  }

  assert !(exists j :: 0 <= j < inputs.Length - 1 && inputs[j] == inputs[j + 1]);
}