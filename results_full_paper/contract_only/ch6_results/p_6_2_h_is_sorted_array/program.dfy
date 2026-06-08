method p_6_2_h_is_sorted_array(inputs: array<int>) returns (is_sorted: bool)
	ensures is_sorted == (forall i :: 0 <= i < inputs.Length - 1 ==> inputs[i] <= inputs[i + 1])
{
  var i := 0;
  while i < inputs.Length - 1
    invariant 0 <= i <= inputs.Length
    invariant forall j :: 0 <= j < i && j + 1 < inputs.Length ==> inputs[j] <= inputs[j + 1]
  {
    if inputs[i] > inputs[i + 1] {
      is_sorted := false;
      assert 0 <= i < inputs.Length - 1;
      assert !(forall j :: 0 <= j < inputs.Length - 1 ==> inputs[j] <= inputs[j + 1]) by {
        if forall j :: 0 <= j < inputs.Length - 1 ==> inputs[j] <= inputs[j + 1] {
          assert inputs[i] <= inputs[i + 1];
          assert false;
        }
      }
      return;
    }

    var old_i := i;
    assert inputs[old_i] <= inputs[old_i + 1];
    i := i + 1;
    assert forall j :: 0 <= j < i && j + 1 < inputs.Length ==> inputs[j] <= inputs[j + 1] by {
      forall j | 0 <= j < i && j + 1 < inputs.Length
        ensures inputs[j] <= inputs[j + 1]
      {
        if j == old_i {
          assert inputs[j] <= inputs[j + 1];
        } else {
          assert j < old_i;
          assert inputs[j] <= inputs[j + 1];
        }
      }
    }
  }

  is_sorted := true;
  assert forall j :: 0 <= j < inputs.Length - 1 ==> inputs[j] <= inputs[j + 1] by {
    forall j | 0 <= j < inputs.Length - 1
      ensures inputs[j] <= inputs[j + 1]
    {
      assert !(i < inputs.Length - 1);
      assert inputs.Length - 1 <= i;
      assert j < i;
      assert j + 1 < inputs.Length;
      assert inputs[j] <= inputs[j + 1];
    }
  }
}