method p_14_2_selection_sort_interval_array(inputs: array<int>, bound: nat) returns (sorted: array<int>)
	requires forall i :: 0 <= i < inputs.Length ==> 0 <= inputs[i] <= bound
	ensures forall i, j :: 0 <= i < j < sorted.Length ==> sorted[i] <= sorted[j]
	ensures multiset(inputs[..]) == multiset(sorted[..])
{
  sorted := new int[inputs.Length];

  var c := 0;
  while c < inputs.Length
    invariant 0 <= c <= inputs.Length
    invariant sorted.Length == inputs.Length
    invariant forall k :: 0 <= k < c ==> sorted[k] == inputs[k]
  {
    sorted[c] := inputs[c];
    c := c + 1;
  }

  forall k: int | 0 <= k < inputs.Length
    ensures sorted[..][k] == inputs[..][k]
  {
    assert sorted[k] == inputs[k];
  }
  assert sorted[..] == inputs[..];

  var n := sorted.Length;
  var i := 0;
  while i < n
    invariant sorted.Length == n
    invariant inputs.Length == n
    invariant 0 <= i <= n
    invariant multiset(sorted[..]) == multiset(inputs[..])
    invariant forall k, l :: 0 <= k < l < i ==> sorted[k] <= sorted[l]
    invariant forall k, l :: 0 <= k < i <= l < n ==> sorted[k] <= sorted[l]
  {
    var min := i;
    var j := i + 1;

    while j < n
      invariant sorted.Length == n
      invariant 0 <= i < j <= n
      invariant i <= min < j
      invariant forall k :: i <= k < j ==> sorted[min] <= sorted[k]
    {
      if sorted[j] < sorted[min] {
        var oldMin := min;
        min := j;
        forall k: int | i <= k < j
          ensures sorted[min] <= sorted[k]
        {
          assert sorted[oldMin] <= sorted[k];
          assert sorted[min] < sorted[oldMin];
        }
      }

      forall k: int | i <= k < j + 1
        ensures sorted[min] <= sorted[k]
      {
        if k < j {
          assert sorted[min] <= sorted[k];
        } else {
          assert k == j;
          assert sorted[min] <= sorted[j];
        }
      }
      j := j + 1;
    }

    ghost var pre := sorted[..];
    ghost var min0 := min;
    ghost var preIVal := pre[i];
    ghost var preMinVal := pre[min0];

    assert i <= min0 < n;
    assert forall k, l :: 0 <= k < l < i ==> pre[k] <= pre[l];
    assert forall k, l :: 0 <= k < i <= l < n ==> pre[k] <= pre[l];
    assert forall k :: i <= k < n ==> preMinVal <= pre[k];

    if min != i {
      assert min == min0;
      assert i < min0 < n;
      var tmp := sorted[i];
      sorted[i] := sorted[min];
      sorted[min] := tmp;

      assert sorted[i] == preMinVal;
      assert sorted[min0] == preIVal;
      assert forall t :: 0 <= t < n && t != i && t != min0 ==> sorted[t] == pre[t];

      ghost var post := sorted[..];
      assert post == pre[i := preMinVal][min0 := preIVal];

      ghost var left := pre[..i];
      ghost var middle := pre[i + 1..min0];
      ghost var right := pre[min0 + 1..];
      assert pre == left + [preIVal] + middle + [preMinVal] + right;
      assert post == left + [preMinVal] + middle + [preIVal] + right;

      calc {
        multiset(post);
      ==
        multiset(left + [preMinVal] + middle + [preIVal] + right);
      ==
        multiset(left) + multiset([preMinVal]) + multiset(middle) + multiset([preIVal]) + multiset(right);
      ==
        multiset(left) + multiset([preIVal]) + multiset(middle) + multiset([preMinVal]) + multiset(right);
      ==
        multiset(left + [preIVal] + middle + [preMinVal] + right);
      ==
        multiset(pre);
      }
      assert multiset(sorted[..]) == multiset(pre);
    } else {
      assert min0 == i;
      assert sorted[..] == pre;
      assert multiset(sorted[..]) == multiset(pre);
    }

    assert sorted[i] == preMinVal;
    assert sorted[min0] == preIVal;
    assert forall t :: 0 <= t < n && t != i && t != min0 ==> sorted[t] == pre[t];
    assert multiset(sorted[..]) == multiset(inputs[..]);

    forall k: int, l: int | 0 <= k < l < i + 1
      ensures sorted[k] <= sorted[l]
    {
      if l < i {
        assert k != i && l != i;
        assert k != min0 && l != min0;
        assert sorted[k] == pre[k];
        assert sorted[l] == pre[l];
        assert pre[k] <= pre[l];
      } else {
        assert l == i;
        assert k < i;
        assert k != min0;
        assert sorted[k] == pre[k];
        assert sorted[i] == preMinVal;
        assert pre[k] <= pre[min0];
      }
    }

    forall k: int, l: int | 0 <= k < i + 1 <= l < n
      ensures sorted[k] <= sorted[l]
    {
      if k < i {
        assert k != i && k != min0;
        assert sorted[k] == pre[k];
        if l == min0 {
          assert min0 != i;
          assert sorted[l] == preIVal;
          assert pre[k] <= pre[i];
        } else {
          assert l != i;
          assert sorted[l] == pre[l];
          assert pre[k] <= pre[l];
        }
      } else {
        assert k == i;
        assert sorted[k] == preMinVal;
        if l == min0 {
          assert min0 != i;
          assert sorted[l] == preIVal;
          assert preMinVal <= pre[i];
        } else {
          assert l != i;
          assert sorted[l] == pre[l];
          assert preMinVal <= pre[l];
        }
      }
    }

    i := i + 1;
  }

  assert i == n;
  assert n == sorted.Length;
  assert forall k, l :: 0 <= k < l < sorted.Length ==> sorted[k] <= sorted[l];
  assert multiset(inputs[..]) == multiset(sorted[..]);
}