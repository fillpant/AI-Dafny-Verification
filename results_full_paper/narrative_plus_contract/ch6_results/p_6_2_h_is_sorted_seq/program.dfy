method p_6_2_h_is_sorted_seq(inputs: seq<int>) returns (is_sorted: bool)
	ensures is_sorted == (forall i :: 0 <= i < |inputs| - 1 ==> inputs[i] <= inputs[i + 1])
{
  if |inputs| < 2 {
    is_sorted := true;
    return;
  }

  var i := 0;
  while i < |inputs| - 1
    invariant 0 <= i <= |inputs| - 1
    invariant forall k :: 0 <= k < i ==> inputs[k] <= inputs[k + 1]
    decreases |inputs| - 1 - i
  {
    if inputs[i] > inputs[i + 1] {
      is_sorted := false;
      assert 0 <= i < |inputs| - 1;
      assert !(inputs[i] <= inputs[i + 1]);
      assert !(forall k :: 0 <= k < |inputs| - 1 ==> inputs[k] <= inputs[k + 1]);
      return;
    }

    forall k | 0 <= k < i + 1
      ensures inputs[k] <= inputs[k + 1]
    {
      if k == i {
        assert inputs[k] <= inputs[k + 1];
      } else {
        assert k < i;
        assert inputs[k] <= inputs[k + 1];
      }
    }

    i := i + 1;
  }

  assert i == |inputs| - 1;
  assert forall k :: 0 <= k < |inputs| - 1 ==> inputs[k] <= inputs[k + 1];
  is_sorted := true;
}