method p_14_2_selection_sort_interval_array(inputs: array<int>, bound: nat) returns (sorted: array<int>)
	requires forall i :: 0 <= i < inputs.Length ==> 0 <= inputs[i] <= bound
	ensures forall i, j :: 0 <= i < j < sorted.Length ==> sorted[i] <= sorted[j]
	ensures multiset(inputs[..]) == multiset(sorted[..])
{
  var n := inputs.Length;
  sorted := new int[n](k => inputs[k]);

  forall k | 0 <= k < n
    ensures sorted[..][k] == inputs[..][k]
  {
    assert sorted[..][k] == sorted[k];
    assert inputs[..][k] == inputs[k];
  }
  assert sorted[..] == inputs[..];
  assert {:split_here} true;

  var i := 0;
  while i < n
    invariant sorted.Length == n
    invariant inputs.Length == n
    invariant 0 <= i <= n
    invariant multiset(sorted[..]) == multiset(inputs[..])
    invariant forall p, q :: 0 <= p < q < i ==> sorted[p] <= sorted[q]
    invariant forall p, q :: 0 <= p < i <= q < n ==> sorted[p] <= sorted[q]
    decreases n - i
  {
    var min := i;
    var j := i + 1;

    while j < n
      invariant sorted.Length == n
      invariant inputs.Length == n
      invariant 0 <= i < n
      invariant i <= min < n
      invariant i + 1 <= j <= n
      invariant multiset(sorted[..]) == multiset(inputs[..])
      invariant forall k :: i <= k < j ==> sorted[min] <= sorted[k]
      invariant forall p, q :: 0 <= p < q < i ==> sorted[p] <= sorted[q]
      invariant forall p, q :: 0 <= p < i <= q < n ==> sorted[p] <= sorted[q]
      decreases n - j
    {
      if sorted[j] < sorted[min] {
        var oldMin := min;
        assert forall k :: i <= k < j ==> sorted[oldMin] <= sorted[k];
        min := j;
        forall k | i <= k < j + 1
          ensures sorted[min] <= sorted[k]
        {
          if k != j {
            assert i <= k < j;
            assert sorted[min] < sorted[oldMin];
            assert sorted[oldMin] <= sorted[k];
          }
        }
      } else {
        forall k | i <= k < j + 1
          ensures sorted[min] <= sorted[k]
        {
          if k == j {
            assert sorted[min] <= sorted[j];
          } else {
            assert i <= k < j;
          }
        }
      }
      j := j + 1;
    }

    assert {:split_here} true;
    ghost var pre := sorted[..];
    assert |pre| == n;
    assert forall k :: i <= k < n ==> pre[min] <= pre[k];
    assert forall p, q :: 0 <= p < q < i ==> pre[p] <= pre[q];
    assert forall p, q :: 0 <= p < i <= q < n ==> pre[p] <= pre[q];

    if min != i {
      assert i < min;
      var tmp := sorted[i];
      sorted[i] := sorted[min];
      sorted[min] := tmp;

      ghost var swapped := pre[i := pre[min]][min := pre[i]];
      forall k | 0 <= k < n
        ensures sorted[..][k] == swapped[k]
      {
        assert sorted[..][k] == sorted[k];
        if k == i {
          assert sorted[k] == pre[min];
          assert swapped[k] == pre[min];
        } else if k == min {
          assert sorted[k] == pre[i];
          assert swapped[k] == pre[i];
        } else {
          assert sorted[k] == pre[k];
          assert swapped[k] == pre[k];
        }
      }
      assert sorted[..] == swapped;

      ghost var A := pre[..i];
      ghost var B := pre[i + 1..min];
      ghost var C := pre[min + 1..];
      assert pre == A + [pre[i]] + B + [pre[min]] + C;
      assert swapped == A + [pre[min]] + B + [pre[i]] + C;
      calc {
        multiset(swapped);
      ==
        multiset(A + [pre[min]] + B + [pre[i]] + C);
      ==
        multiset(A) + multiset([pre[min]]) + multiset(B) + multiset([pre[i]]) + multiset(C);
      ==
        multiset(A) + multiset([pre[i]]) + multiset(B) + multiset([pre[min]]) + multiset(C);
      ==
        multiset(A + [pre[i]] + B + [pre[min]] + C);
      ==
        multiset(pre);
      }
      assert multiset(sorted[..]) == multiset(pre);
    } else {
      assert sorted[..] == pre;
      assert multiset(sorted[..]) == multiset(pre);
    }

    assert {:split_here} true;
    assert sorted[..] == pre[i := pre[min]][min := pre[i]];
    assert sorted[i] == pre[min];
    assert sorted[min] == pre[i];
    forall k | 0 <= k < n && k != i && k != min
      ensures sorted[k] == pre[k]
    {
      assert sorted[..][k] == (pre[i := pre[min]][min := pre[i]])[k];
    }
    assert multiset(sorted[..]) == multiset(inputs[..]);

    forall q | i + 1 <= q < n
      ensures sorted[i] <= sorted[q]
    {
      if q == min {
        assert sorted[q] == pre[i];
        assert pre[min] <= pre[i];
      } else {
        assert sorted[q] == pre[q];
        assert pre[min] <= pre[q];
      }
    }

    forall p, q | 0 <= p < q < i + 1
      ensures sorted[p] <= sorted[q]
    {
      if q < i {
        assert sorted[p] == pre[p];
        assert sorted[q] == pre[q];
        assert pre[p] <= pre[q];
      } else {
        assert q == i;
        assert p < i;
        assert sorted[p] == pre[p];
        assert sorted[i] == pre[min];
        assert pre[p] <= pre[min];
      }
    }

    forall p, q | 0 <= p < i + 1 <= q < n
      ensures sorted[p] <= sorted[q]
    {
      if p < i {
        assert sorted[p] == pre[p];
        if q == min {
          assert sorted[q] == pre[i];
          assert pre[p] <= pre[i];
        } else {
          assert sorted[q] == pre[q];
          assert pre[p] <= pre[q];
        }
      } else {
        assert p == i;
        assert sorted[i] == pre[min];
        if q == min {
          assert sorted[q] == pre[i];
          assert pre[min] <= pre[i];
        } else {
          assert sorted[q] == pre[q];
          assert pre[min] <= pre[q];
        }
      }
    }

    i := i + 1;
  }

  assert forall p, q :: 0 <= p < q < sorted.Length ==> sorted[p] <= sorted[q];
  assert multiset(inputs[..]) == multiset(sorted[..]);
}