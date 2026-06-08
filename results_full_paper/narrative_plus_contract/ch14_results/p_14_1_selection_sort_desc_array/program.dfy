method p_14_1_selection_sort_desc_array(inputs: array<int>) returns (sorted: array<int>)
	ensures forall i, j :: 0 <= i < j < sorted.Length ==> sorted[i] >= sorted[j]
	ensures multiset(inputs[..]) == multiset(sorted[..])
{
  sorted := new int[inputs.Length];
  var n := inputs.Length;

  var c := 0;
  while c < n
    invariant 0 <= c <= n
    invariant n == inputs.Length
    invariant sorted.Length == n
    invariant forall k :: 0 <= k < c ==> sorted[k] == inputs[k]
  {
    sorted[c] := inputs[c];
    c := c + 1;
  }
  assert forall k :: 0 <= k < n ==> sorted[k] == inputs[k];
  assert sorted[..] == inputs[..];
  assert multiset(sorted[..]) == multiset(inputs[..]);

  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant n == inputs.Length
    invariant sorted.Length == n
    invariant multiset(sorted[..]) == multiset(inputs[..])
    invariant forall p, q :: 0 <= p < q < i ==> sorted[p] >= sorted[q]
    invariant forall p, q :: 0 <= p < i <= q < n ==> sorted[p] >= sorted[q]
  {
    var maxIdx := i;
    var j := i + 1;
    while j < n
      invariant 0 <= i < n
      invariant i + 1 <= j <= n
      invariant i <= maxIdx < j
      invariant n == inputs.Length
      invariant sorted.Length == n
      invariant multiset(sorted[..]) == multiset(inputs[..])
      invariant forall p, q :: 0 <= p < q < i ==> sorted[p] >= sorted[q]
      invariant forall p, q :: 0 <= p < i <= q < n ==> sorted[p] >= sorted[q]
      invariant forall k :: i <= k < j ==> sorted[maxIdx] >= sorted[k]
    {
      if sorted[j] > sorted[maxIdx] {
        forall k | i <= k < j
          ensures sorted[j] >= sorted[k]
        {
          assert sorted[maxIdx] >= sorted[k];
        }
        maxIdx := j;
      } else {
        assert sorted[maxIdx] >= sorted[j];
      }
      forall k | i <= k < j + 1
        ensures sorted[maxIdx] >= sorted[k]
      {
        if k < j {
          assert sorted[maxIdx] >= sorted[k];
        } else {
          assert k == j;
        }
      }
      j := j + 1;
    }

    assert j == n;
    ghost var a := sorted[..];
    assert |a| == n;
    assert multiset(a) == multiset(inputs[..]);
    forall k | i <= k < n
      ensures a[maxIdx] >= a[k]
    {
      assert sorted[maxIdx] >= sorted[k];
    }
    forall p, q | 0 <= p < q < i
      ensures a[p] >= a[q]
    {
      assert sorted[p] >= sorted[q];
    }
    forall p, q | 0 <= p < i <= q < n
      ensures a[p] >= a[q]
    {
      assert sorted[p] >= sorted[q];
    }

    if maxIdx != i {
      sorted[i], sorted[maxIdx] := sorted[maxIdx], sorted[i];
      assert sorted[..] == a[i := a[maxIdx]][maxIdx := a[i]];
      assert multiset(sorted[..]) == multiset(a);
    } else {
      assert sorted[..] == a;
    }
    assert multiset(sorted[..]) == multiset(a);
    assert multiset(sorted[..]) == multiset(inputs[..]);

    assert sorted[i] == a[maxIdx];
    assert sorted[maxIdx] == a[i];
    forall k | 0 <= k < n && k != i && k != maxIdx
      ensures sorted[k] == a[k]
    {
    }

    var ni := i + 1;
    assert ni <= n;

    forall p, q | 0 <= p < q < ni
      ensures sorted[p] >= sorted[q]
    {
      if q < i {
        assert a[p] >= a[q];
        assert p != i && p != maxIdx;
        assert q != i && q != maxIdx;
        assert sorted[p] == a[p];
        assert sorted[q] == a[q];
      } else {
        assert q == i;
        assert p < i;
        assert i <= maxIdx < n;
        assert a[p] >= a[maxIdx];
        assert p != i && p != maxIdx;
        assert sorted[p] == a[p];
        assert sorted[q] == a[maxIdx];
      }
    }

    forall p, q | 0 <= p < ni <= q < n
      ensures sorted[p] >= sorted[q]
    {
      if p < i {
        assert p != i && p != maxIdx;
        assert sorted[p] == a[p];
        if q == maxIdx {
          assert sorted[q] == a[i];
          assert a[p] >= a[i];
        } else {
          assert q != i;
          assert sorted[q] == a[q];
          assert a[p] >= a[q];
        }
      } else {
        assert p == i;
        assert sorted[p] == a[maxIdx];
        if q == maxIdx {
          assert sorted[q] == a[i];
          assert a[maxIdx] >= a[i];
        } else {
          assert q != i;
          assert sorted[q] == a[q];
          assert a[maxIdx] >= a[q];
        }
      }
    }

    i := ni;
  }

  assert i == n;
  assert sorted.Length == n;
  assert forall p, q :: 0 <= p < q < sorted.Length ==> sorted[p] >= sorted[q];
  assert multiset(inputs[..]) == multiset(sorted[..]);
}