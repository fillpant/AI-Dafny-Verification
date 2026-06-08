method p_14_4_merge_sort_lexicographic_array(inputs: array<string>) returns (sorted: array<string>)
	ensures forall i, j :: 0 <= i < j < sorted.Length ==> sorted[i] <= sorted[j]
	ensures multiset(inputs[..]) == multiset(sorted[..])
{
  var n := inputs.Length;
  sorted := new string[n](i => "");

  var c := 0;
  while c < n
    invariant 0 <= c <= n
    invariant sorted.Length == n
    invariant forall k :: 0 <= k < c ==> sorted[k] == inputs[k]
    decreases n - c
  {
    sorted[c] := inputs[c];
    c := c + 1;
  }

  forall k | 0 <= k < n
    ensures sorted[..][k] == inputs[..][k]
  {
    assert sorted[..][k] == sorted[k];
    assert inputs[..][k] == inputs[k];
  }
  assert sorted[..] == inputs[..];

  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant sorted.Length == n
    invariant forall p, q :: 0 <= p < q < i ==> sorted[p] <= sorted[q]
    invariant forall p, q :: 0 <= p < i && i <= q < n ==> sorted[p] <= sorted[q]
    invariant multiset(sorted[..]) == multiset(inputs[..])
    decreases n - i
  {
    var m := i;
    var j := i + 1;
    while j < n
      invariant i < n
      invariant i + 1 <= j <= n
      invariant i <= m < n
      invariant sorted.Length == n
      invariant forall k :: i <= k < j ==> sorted[m] <= sorted[k]
      invariant forall p, q :: 0 <= p < q < i ==> sorted[p] <= sorted[q]
      invariant forall p, q :: 0 <= p < i && i <= q < n ==> sorted[p] <= sorted[q]
      invariant multiset(sorted[..]) == multiset(inputs[..])
      decreases n - j
    {
      if sorted[j] <= sorted[m] {
        var oldM := m;
        forall k | i <= k < j + 1
          ensures sorted[j] <= sorted[k]
        {
          if k == j {
          } else {
            assert i <= k < j;
            assert sorted[oldM] <= sorted[k];
            assert sorted[j] <= sorted[oldM];
          }
        }
        m := j;
      } else {
        assert sorted[m] <= sorted[j];
        forall k | i <= k < j + 1
          ensures sorted[m] <= sorted[k]
        {
          if k == j {
          } else {
            assert i <= k < j;
          }
        }
      }
      j := j + 1;
    }

    ghost var oldSeq := sorted[..];

    forall k | i <= k < n
      ensures oldSeq[m] <= oldSeq[k]
    {
      assert sorted[m] <= sorted[k];
      assert oldSeq[m] == sorted[m];
      assert oldSeq[k] == sorted[k];
    }
    forall p, q | 0 <= p < q < i
      ensures oldSeq[p] <= oldSeq[q]
    {
      assert oldSeq[p] == sorted[p];
      assert oldSeq[q] == sorted[q];
    }
    forall p, q | 0 <= p < i && i <= q < n
      ensures oldSeq[p] <= oldSeq[q]
    {
      assert oldSeq[p] == sorted[p];
      assert oldSeq[q] == sorted[q];
    }

    if m != i {
      var tmp := sorted[i];
      sorted[i] := sorted[m];
      sorted[m] := tmp;

      assert sorted[i] == oldSeq[m];
      assert sorted[m] == oldSeq[i];
      forall k | 0 <= k < n && k != i && k != m
        ensures sorted[k] == oldSeq[k]
      {
      }

      forall k | 0 <= k < n
        ensures sorted[..][k] == (oldSeq[i := oldSeq[m]][m := oldSeq[i]])[k]
      {
        assert sorted[..][k] == sorted[k];
        if k == i {
          assert (oldSeq[i := oldSeq[m]])[i] == oldSeq[m];
          assert (oldSeq[i := oldSeq[m]][m := oldSeq[i]])[i] == oldSeq[m];
        } else if k == m {
          assert (oldSeq[i := oldSeq[m]][m := oldSeq[i]])[m] == oldSeq[i];
        } else {
          assert k != i && k != m;
          assert (oldSeq[i := oldSeq[m]])[k] == oldSeq[k];
          assert (oldSeq[i := oldSeq[m]][m := oldSeq[i]])[k] == oldSeq[k];
        }
      }
      assert sorted[..] == oldSeq[i := oldSeq[m]][m := oldSeq[i]];
      assert multiset(oldSeq[i := oldSeq[m]]) == multiset(oldSeq) - multiset{oldSeq[i]} + multiset{oldSeq[m]};
      assert (oldSeq[i := oldSeq[m]])[m] == oldSeq[m];
      assert multiset((oldSeq[i := oldSeq[m]])[m := oldSeq[i]]) == multiset(oldSeq[i := oldSeq[m]]) - multiset{oldSeq[m]} + multiset{oldSeq[i]};
      assert multiset(sorted[..]) == multiset(oldSeq);
    } else {
      assert sorted[..] == oldSeq;
      assert multiset(sorted[..]) == multiset(oldSeq);
    }

    assert sorted[i] == oldSeq[m];
    assert sorted[m] == oldSeq[i];
    forall k | 0 <= k < n && k != i && k != m
      ensures sorted[k] == oldSeq[k]
    {
      if m == i {
        assert sorted[..] == oldSeq;
        assert sorted[..][k] == sorted[k];
      }
    }

    assert multiset(sorted[..]) == multiset(inputs[..]);

    forall p, q | 0 <= p < q < i + 1
      ensures sorted[p] <= sorted[q]
    {
      if q < i {
        assert p < q < i;
        assert p != i && p != m;
        assert q != i && q != m;
        assert sorted[p] == oldSeq[p];
        assert sorted[q] == oldSeq[q];
        assert oldSeq[p] <= oldSeq[q];
      } else {
        assert q == i;
        assert p < i;
        assert p != i && p != m;
        assert sorted[p] == oldSeq[p];
        assert sorted[q] == oldSeq[m];
        assert i <= m < n;
        assert oldSeq[p] <= oldSeq[m];
      }
    }

    forall p, q | 0 <= p < i + 1 && i + 1 <= q < n
      ensures sorted[p] <= sorted[q]
    {
      if p < i {
        assert p != i && p != m;
        assert sorted[p] == oldSeq[p];
        if q == m {
          assert sorted[q] == oldSeq[i];
          assert oldSeq[p] <= oldSeq[i];
        } else {
          assert q != i && q != m;
          assert sorted[q] == oldSeq[q];
          assert oldSeq[p] <= oldSeq[q];
        }
      } else {
        assert p == i;
        assert sorted[p] == oldSeq[m];
        if q == m {
          assert sorted[q] == oldSeq[i];
          assert oldSeq[m] <= oldSeq[i];
        } else {
          assert q != i && q != m;
          assert sorted[q] == oldSeq[q];
          assert oldSeq[m] <= oldSeq[q];
        }
      }
    }

    i := i + 1;
  }

  assert sorted.Length == n;
  forall p, q | 0 <= p < q < sorted.Length
    ensures sorted[p] <= sorted[q]
  {
    assert 0 <= p < q < n;
  }
  assert multiset(inputs[..]) == multiset(sorted[..]);
}