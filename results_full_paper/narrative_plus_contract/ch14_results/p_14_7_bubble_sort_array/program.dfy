method p_14_4_bubble_sort_array(inputs: array<int>) returns (sorted: array<int>)
	ensures forall i, j :: 0 <= i < j < sorted.Length ==> sorted[i] <= sorted[j]
	ensures multiset(inputs[..]) == multiset(sorted[..])
{
  var n := inputs.Length;
  sorted := new int[n];

  var k := 0;
  while k < n
    invariant 0 <= k <= n
    invariant sorted.Length == n
    invariant forall t :: 0 <= t < k ==> sorted[t] == inputs[t]
    decreases n - k
  {
    sorted[k] := inputs[k];
    k := k + 1;
  }

  assert forall t | 0 <= t < n :: sorted[t] == inputs[t];
  assert |sorted[..]| == |inputs[..]|;
  assert forall t :: 0 <= t < |sorted[..]| ==> sorted[..][t] == inputs[..][t];
  assert sorted[..] == inputs[..];
  assert multiset(sorted[..]) == multiset(inputs[..]);

  var end := n;
  while 1 < end
    invariant 0 <= end <= n
    invariant sorted.Length == n
    invariant multiset(sorted[..]) == multiset(inputs[..])
    invariant forall i, j :: end <= i < j < n ==> sorted[i] <= sorted[j]
    invariant forall i, j :: 0 <= i < end <= j < n ==> sorted[i] <= sorted[j]
    decreases end
  {
    var j := 0;
    while j + 1 < end
      invariant 0 <= j < end <= n
      invariant sorted.Length == n
      invariant multiset(sorted[..]) == multiset(inputs[..])
      invariant forall i, k :: end <= i < k < n ==> sorted[i] <= sorted[k]
      invariant forall i, k :: 0 <= i < end <= k < n ==> sorted[i] <= sorted[k]
      invariant forall i :: 0 <= i <= j ==> sorted[i] <= sorted[j]
      decreases end - j
    {
      if sorted[j] > sorted[j + 1] {
        ghost var s0 := sorted[..];
        assert |s0| == n;
        assert s0[j] > s0[j + 1];
        assert multiset(s0) == multiset(inputs[..]);
        assert forall p | 0 <= p <= j :: s0[p] <= s0[j];
        assert forall p, q | end <= p < q < n :: s0[p] <= s0[q];
        assert forall p, q | 0 <= p < end <= q < n :: s0[p] <= s0[q];

        var tmp := sorted[j];
        sorted[j] := sorted[j + 1];
        sorted[j + 1] := tmp;

        assert j + 2 <= n;
        assert s0 == s0[..j] + [s0[j]] + [s0[j + 1]] + s0[j + 2..];
        assert sorted[..j] == s0[..j];
        assert sorted[j] == s0[j + 1];
        assert sorted[j + 1] == s0[j];
        assert sorted[j + 2..] == s0[j + 2..];
        assert sorted[..] == s0[..j] + [s0[j + 1]] + [s0[j]] + s0[j + 2..];
        calc {
          multiset(sorted[..]);
        == {
          assert sorted[..] == s0[..j] + [s0[j + 1]] + [s0[j]] + s0[j + 2..];
        }
          multiset(s0[..j] + [s0[j + 1]] + [s0[j]] + s0[j + 2..]);
        == { }
          multiset(s0[..j]) + multiset([s0[j + 1]]) + multiset([s0[j]]) + multiset(s0[j + 2..]);
        == { }
          multiset(s0[..j]) + multiset([s0[j]]) + multiset([s0[j + 1]]) + multiset(s0[j + 2..]);
        == {
          assert s0 == s0[..j] + [s0[j]] + [s0[j + 1]] + s0[j + 2..];
        }
          multiset(s0);
        == {
          assert multiset(s0) == multiset(inputs[..]);
        }
          multiset(inputs[..]);
        }

        forall p | 0 <= p <= j + 1
          ensures sorted[p] <= sorted[j + 1]
        {
          if p < j {
            assert sorted[p] == s0[p];
            assert s0[p] <= s0[j];
            assert sorted[j + 1] == s0[j];
          } else if p == j {
            assert sorted[p] == s0[j + 1];
            assert sorted[j + 1] == s0[j];
            assert s0[j + 1] < s0[j];
          } else {
            assert p == j + 1;
          }
        }
        forall p, q | end <= p < q < n
          ensures sorted[p] <= sorted[q]
        {
          assert p != j && p != j + 1;
          assert q != j && q != j + 1;
          assert sorted[p] == s0[p];
          assert sorted[q] == s0[q];
          assert s0[p] <= s0[q];
        }
        forall p, q | 0 <= p < end <= q < n
          ensures sorted[p] <= sorted[q]
        {
          assert q != j && q != j + 1;
          assert sorted[q] == s0[q];
          if p == j {
            assert sorted[p] == s0[j + 1];
            assert s0[j + 1] <= s0[q];
          } else if p == j + 1 {
            assert sorted[p] == s0[j];
            assert s0[j] <= s0[q];
          } else {
            assert sorted[p] == s0[p];
            assert s0[p] <= s0[q];
          }
        }
        assert multiset(sorted[..]) == multiset(inputs[..]);
      } else {
        assert sorted[j] <= sorted[j + 1];
        forall p | 0 <= p <= j + 1
          ensures sorted[p] <= sorted[j + 1]
        {
          if p <= j {
            assert sorted[p] <= sorted[j];
            assert sorted[j] <= sorted[j + 1];
          } else {
            assert p == j + 1;
          }
        }
        assert forall p, q | end <= p < q < n :: sorted[p] <= sorted[q];
        assert forall p, q | 0 <= p < end <= q < n :: sorted[p] <= sorted[q];
        assert multiset(sorted[..]) == multiset(inputs[..]);
      }

      j := j + 1;
    }

    assert j == end - 1;
    forall p, q | end - 1 <= p < q < n
      ensures sorted[p] <= sorted[q]
    {
      if p == end - 1 {
        assert p == j;
        assert end <= q;
        assert 0 <= p < end <= q < n;
        assert sorted[p] <= sorted[q];
      } else {
        assert end <= p;
        assert sorted[p] <= sorted[q];
      }
    }
    forall p, q | 0 <= p < end - 1 <= q < n
      ensures sorted[p] <= sorted[q]
    {
      if q == end - 1 {
        assert q == j;
        assert 0 <= p <= j;
        assert sorted[p] <= sorted[j];
      } else {
        assert end <= q;
        assert p < end;
        assert sorted[p] <= sorted[q];
      }
    }

    end := end - 1;
  }

  forall i, j | 0 <= i < j < n
    ensures sorted[i] <= sorted[j]
  {
    if end <= i {
      assert sorted[i] <= sorted[j];
    } else {
      assert i < end;
      assert end <= 1;
      if end == 0 {
        assert !(0 <= i < end);
      } else {
        assert end == 1;
        assert i == 0;
        assert end <= j;
        assert sorted[i] <= sorted[j];
      }
    }
  }
  assert sorted.Length == n;
  assert multiset(sorted[..]) == multiset(inputs[..]);
}