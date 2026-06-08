method p_14_4_bubble_sort_array(inputs: array<int>) returns (sorted: array<int>)
	ensures forall i, j :: 0 <= i < j < sorted.Length ==> sorted[i] <= sorted[j]
	ensures multiset(inputs[..]) == multiset(sorted[..])
{
  var n := inputs.Length;
  sorted := new int[n](k => inputs[k]);

  assert sorted.Length == n;
  assert forall k :: 0 <= k < n ==> sorted[k] == inputs[k];
  assert sorted[..] == inputs[..];
  assert multiset(sorted[..]) == multiset(inputs[..]);

  var i := n;
  while i > 0
    invariant 0 <= i <= n
    invariant sorted.Length == n
    invariant multiset(sorted[..]) == multiset(inputs[..])
    invariant forall p, q :: i <= p < q < n ==> sorted[p] <= sorted[q]
    invariant forall p, q :: 0 <= p < i <= q < n ==> sorted[p] <= sorted[q]
    decreases i
  {
    var j := 1;
    while j < i
      invariant 1 <= j <= i
      invariant sorted.Length == n
      invariant multiset(sorted[..]) == multiset(inputs[..])
      invariant forall p, q :: i <= p < q < n ==> sorted[p] <= sorted[q]
      invariant forall p, q :: 0 <= p < i <= q < n ==> sorted[p] <= sorted[q]
      invariant forall k :: 0 <= k < j ==> sorted[k] <= sorted[j - 1]
      decreases i - j
    {
      ghost var before := sorted[..];
      assert before == sorted[..];
      assert |before| == n;
      assert multiset(before) == multiset(inputs[..]);
      assert forall k :: 0 <= k < j ==> before[k] <= before[j - 1];
      assert forall p, q :: i <= p < q < n ==> before[p] <= before[q];
      assert forall p, q :: 0 <= p < i <= q < n ==> before[p] <= before[q];

      if before[j] < before[j - 1] {
        var t := sorted[j - 1];
        sorted[j - 1] := sorted[j];
        sorted[j] := t;

        assert sorted[j - 1] == before[j];
        assert sorted[j] == before[j - 1];

        ghost var swapped := before[..j - 1] + [before[j]] + [before[j - 1]] + before[j + 1..];
        assert |swapped| == |before|;
        forall k | 0 <= k < sorted.Length
          ensures sorted[k] == swapped[k]
        {
          if k < j - 1 {
            assert sorted[k] == before[k];
            assert swapped[k] == before[k];
          } else if k == j - 1 {
            assert sorted[k] == before[j];
            assert swapped[k] == before[j];
          } else if k == j {
            assert sorted[k] == before[j - 1];
            assert swapped[k] == before[j - 1];
          } else {
            assert j + 1 <= k < sorted.Length;
            assert sorted[k] == before[k];
            assert swapped[k] == before[k];
          }
        }
        assert |sorted[..]| == |swapped|;
        assert forall k :: 0 <= k < |sorted[..]| ==> sorted[..][k] == swapped[k];
        assert sorted[..] == swapped;

        calc {
          multiset(sorted[..]);
        ==
          multiset(swapped);
        ==
          multiset(before[..j - 1] + [before[j]] + [before[j - 1]] + before[j + 1..]);
        ==
          multiset(before[..j - 1]) + multiset([before[j]]) + multiset([before[j - 1]]) + multiset(before[j + 1..]);
        ==
          multiset(before[..j - 1]) + multiset([before[j - 1]]) + multiset([before[j]]) + multiset(before[j + 1..]);
        ==
          multiset(before[..j - 1] + [before[j - 1]] + [before[j]] + before[j + 1..]);
        == {
          assert before == before[..j - 1] + [before[j - 1]] + [before[j]] + before[j + 1..];
        }
          multiset(before);
        }
      } else {
        assert sorted[..] == before;
        assert multiset(sorted[..]) == multiset(before);
      }

      assert multiset(sorted[..]) == multiset(inputs[..]);

      forall p, q | i <= p < q < n
        ensures sorted[p] <= sorted[q]
      {
        assert sorted[p] == before[p];
        assert sorted[q] == before[q];
        assert before[p] <= before[q];
      }

      forall p, q | 0 <= p < i <= q < n
        ensures sorted[p] <= sorted[q]
      {
        if before[j] < before[j - 1] {
          if p == j - 1 {
            assert sorted[p] == before[j];
            assert before[j] <= before[q];
          } else if p == j {
            assert sorted[p] == before[j - 1];
            assert before[j - 1] <= before[q];
          } else {
            assert sorted[p] == before[p];
            assert before[p] <= before[q];
          }
        } else {
          assert sorted[p] == before[p];
          assert before[p] <= before[q];
        }
        assert sorted[q] == before[q];
      }

      forall k | 0 <= k < j + 1
        ensures sorted[k] <= sorted[j]
      {
        if before[j] < before[j - 1] {
          assert sorted[j] == before[j - 1];
          if k == j {
          } else if k == j - 1 {
            assert sorted[k] == before[j];
            assert before[j] < before[j - 1];
          } else {
            assert 0 <= k < j;
            assert sorted[k] == before[k];
            assert before[k] <= before[j - 1];
          }
        } else {
          assert before[j - 1] <= before[j];
          assert sorted[j] == before[j];
          if k == j {
          } else {
            assert 0 <= k < j;
            assert sorted[k] == before[k];
            assert before[k] <= before[j - 1];
            assert before[k] <= before[j];
          }
        }
      }

      j := j + 1;
    }

    assert j == i;
    assert forall k :: 0 <= k < i ==> sorted[k] <= sorted[i - 1];

    forall p, q | i - 1 <= p < q < n
      ensures sorted[p] <= sorted[q]
    {
      if p == i - 1 {
        if q < i {
          assert q == i - 1;
        } else {
          assert i <= q < n;
          assert 0 <= i - 1 < i <= q < n;
          assert sorted[i - 1] <= sorted[q];
        }
      } else {
        assert i <= p < q < n;
        assert sorted[p] <= sorted[q];
      }
    }

    forall p, q | 0 <= p < i - 1 <= q < n
      ensures sorted[p] <= sorted[q]
    {
      if q == i - 1 {
        assert 0 <= p < i;
        assert sorted[p] <= sorted[i - 1];
      } else {
        assert i <= q < n;
        assert 0 <= p < i <= q < n;
        assert sorted[p] <= sorted[q];
      }
    }

    i := i - 1;
  }

  assert i == 0;
  assert forall p, q :: 0 <= p < q < sorted.Length ==> sorted[p] <= sorted[q];
  assert multiset(inputs[..]) == multiset(sorted[..]);
}