method p_6_2_h_is_sorted_array(inputs: array<int>) returns (is_sorted: bool)
	ensures is_sorted == (forall i :: 0 <= i < inputs.Length - 1 ==> inputs[i] <= inputs[i + 1])
{
  is_sorted := true;
  var n := inputs.Length;
  var i := 0;

  while i < n - 1
    invariant n == inputs.Length
    invariant 0 <= n
    invariant 0 <= i
    invariant n == 0 ==> i == 0
    invariant n > 0 ==> i <= n - 1
    invariant is_sorted ==> (forall j :: 0 <= j < i ==> inputs[j] <= inputs[j + 1])
    invariant !is_sorted ==> (exists j :: 0 <= j < i && inputs[j] > inputs[j + 1])
    decreases n - i
  {
    assert n > 0;
    assert i + 1 < n;

    if inputs[i] > inputs[i + 1] {
      is_sorted := false;
      assert 0 <= i < i + 1 && inputs[i] > inputs[i + 1];
      assert (exists j :: 0 <= j < i + 1 && inputs[j] > inputs[j + 1]);
    } else {
      assert inputs[i] <= inputs[i + 1];
      if is_sorted {
        assert (forall j :: 0 <= j < i + 1 ==> inputs[j] <= inputs[j + 1]) by {
          forall j | 0 <= j < i + 1
            ensures inputs[j] <= inputs[j + 1]
          {
            if j < i {
              assert inputs[j] <= inputs[j + 1];
            } else {
              assert j == i;
              assert inputs[i] <= inputs[i + 1];
            }
          }
        }
      } else {
        assert (exists j :: 0 <= j < i && inputs[j] > inputs[j + 1]);
        var j :| 0 <= j < i && inputs[j] > inputs[j + 1];
        assert 0 <= j < i + 1 && inputs[j] > inputs[j + 1];
        assert (exists k :: 0 <= k < i + 1 && inputs[k] > inputs[k + 1]);
      }
    }

    i := i + 1;
  }

  assert !(i < n - 1);
  if n > 0 {
    assert i == n - 1;
  }

  if is_sorted {
    assert (forall k :: 0 <= k < n - 1 ==> inputs[k] <= inputs[k + 1]) by {
      forall k | 0 <= k < n - 1
        ensures inputs[k] <= inputs[k + 1]
      {
        if n == 0 {
          assert false;
        } else {
          assert i == n - 1;
          assert k < i;
          assert inputs[k] <= inputs[k + 1];
        }
      }
    }
  } else {
    assert (exists j :: 0 <= j < i && inputs[j] > inputs[j + 1]);
    var j :| 0 <= j < i && inputs[j] > inputs[j + 1];
    if n == 0 {
      assert i == 0;
      assert false;
    } else {
      assert i == n - 1;
    }
    assert 0 <= j < n - 1 && inputs[j] > inputs[j + 1];
    assert !(inputs[j] <= inputs[j + 1]);
    if (forall k :: 0 <= k < n - 1 ==> inputs[k] <= inputs[k + 1]) {
      assert inputs[j] <= inputs[j + 1];
      assert false;
    }
    assert !(forall k :: 0 <= k < n - 1 ==> inputs[k] <= inputs[k + 1]);
  }

  assert n == inputs.Length;
  assert is_sorted == (forall k :: 0 <= k < inputs.Length - 1 ==> inputs[k] <= inputs[k + 1]);
}