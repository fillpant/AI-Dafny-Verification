method p_14_1_selection_sort_desc_array(inputs: array<int>) returns (sorted: array<int>)
	ensures forall i, j :: 0 <= i < j < sorted.Length ==> sorted[i] >= sorted[j]
	ensures multiset(inputs[..]) == multiset(sorted[..])
{
  var s := inputs[..];
  var n := |s|;

  var i := 0;
  while i < n
    invariant |s| == n
    invariant n == inputs.Length
    invariant 0 <= i <= n
    invariant forall a, b :: 0 <= a < b < i ==> s[a] >= s[b]
    invariant forall a, b :: 0 <= a < i <= b < n ==> s[a] >= s[b]
    invariant multiset(s) == multiset(inputs[..])
    decreases n - i
  {
    var maxIdx := i;
    var j := i + 1;
    while j < n
      invariant |s| == n
      invariant n == inputs.Length
      invariant 0 <= i < n
      invariant i <= maxIdx < j <= n
      invariant forall k :: i <= k < j ==> s[maxIdx] >= s[k]
      invariant forall a, b :: 0 <= a < b < i ==> s[a] >= s[b]
      invariant forall a, b :: 0 <= a < i <= b < n ==> s[a] >= s[b]
      invariant multiset(s) == multiset(inputs[..])
      decreases n - j
    {
      if s[j] > s[maxIdx] {
        maxIdx := j;
      }
      j := j + 1;
    }

    assert j == n;
    var prev := s;
    var vi := prev[i];
    var vmax := prev[maxIdx];
    assert forall k :: i <= k < n ==> prev[maxIdx] >= prev[k];

    s := prev[i := vmax][maxIdx := vi];
    assert |s| == n;

    if maxIdx == i {
      assert vi == vmax;
      assert prev[i := vmax] == prev;
      assert s == prev[i := vi];
      assert prev[i := vi] == prev;
      assert s == prev;
    } else {
      assert i < maxIdx;
      var mid := prev[i := vmax];
      assert s == mid[maxIdx := vi];
      assert mid[maxIdx] == vmax;

      if vi == vmax {
        assert mid == prev;
        assert s == prev[maxIdx := vi];
        assert prev[maxIdx := vi] == prev;
        assert s == prev;
      } else {
        assert multiset(mid) == multiset(prev) - multiset{vi} + multiset{vmax};
        assert multiset(s) == multiset(mid) - multiset{vmax} + multiset{vi};
        assert multiset(s) == multiset(prev);
      }

      assert s[i] == prev[maxIdx];
      assert s[maxIdx] == prev[i];
      forall k | 0 <= k < n && k != i && k != maxIdx
        ensures s[k] == prev[k]
      {
        assert mid[k] == prev[k];
        assert s[k] == mid[k];
      }
    }

    assert s[i] == prev[maxIdx];
    assert s[maxIdx] == prev[i];
    assert forall k :: 0 <= k < n && k != i && k != maxIdx ==> s[k] == prev[k];
    assert multiset(s) == multiset(prev);
    assert multiset(s) == multiset(inputs[..]);

    var next := i + 1;

    forall a, b | 0 <= a < b < next
      ensures s[a] >= s[b]
    {
      if b < i {
        assert a != i && a != maxIdx;
        assert b != i && b != maxIdx;
        assert s[a] == prev[a];
        assert s[b] == prev[b];
        assert prev[a] >= prev[b];
      } else {
        assert b == i;
        assert a < i;
        assert a != i && a != maxIdx;
        assert s[a] == prev[a];
        assert s[b] == prev[maxIdx];
        assert prev[a] >= prev[maxIdx];
      }
    }

    forall a, b | 0 <= a < next <= b < n
      ensures s[a] >= s[b]
    {
      if a < i {
        assert a != i && a != maxIdx;
        assert s[a] == prev[a];
        if b == maxIdx {
          assert s[b] == prev[i];
          assert prev[a] >= prev[i];
        } else {
          assert b != i;
          assert s[b] == prev[b];
          assert prev[a] >= prev[b];
        }
      } else {
        assert a == i;
        assert s[a] == prev[maxIdx];
        if b == maxIdx {
          assert s[b] == prev[i];
          assert prev[maxIdx] >= prev[i];
        } else {
          assert b != i;
          assert s[b] == prev[b];
          assert prev[maxIdx] >= prev[b];
        }
      }
    }

    i := next;
  }

  assert i == n;
  sorted := new int[n];
  assert sorted.Length == n;
  assert sorted != inputs;

  var k := 0;
  while k < n
    invariant sorted.Length == n
    invariant sorted != inputs
    invariant |s| == n
    invariant i == n
    invariant 0 <= k <= n
    invariant forall t :: 0 <= t < k ==> sorted[t] == s[t]
    invariant forall a, b :: 0 <= a < b < n ==> s[a] >= s[b]
    invariant multiset(s) == multiset(inputs[..])
    decreases n - k
  {
    sorted[k] := s[k];
    k := k + 1;
  }

  assert forall t :: 0 <= t < n ==> sorted[t] == s[t];
  assert |sorted[..]| == |s|;
  forall t | 0 <= t < |s|
    ensures sorted[..][t] == s[t]
  {
    assert sorted[..][t] == sorted[t];
    assert sorted[t] == s[t];
  }
  assert sorted[..] == s;

  forall a, b | 0 <= a < b < sorted.Length
    ensures sorted[a] >= sorted[b]
  {
    assert sorted.Length == n;
    assert sorted[a] == s[a];
    assert sorted[b] == s[b];
    assert s[a] >= s[b];
  }

  assert multiset(sorted[..]) == multiset(s);
  assert multiset(inputs[..]) == multiset(sorted[..]);
}