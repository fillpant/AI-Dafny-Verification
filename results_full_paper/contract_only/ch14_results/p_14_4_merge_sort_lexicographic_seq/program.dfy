method p_14_4_merge_sort_lexicographic_seq(inputs: seq<string>) returns (sorted: seq<string>)
	ensures forall i, j :: 0 <= i < j < |sorted| ==> sorted[i] <= sorted[j]
	ensures multiset(inputs) == multiset(sorted)
{
  sorted := [];
  var n := 0;
  while n < |inputs|
    invariant 0 <= n <= |inputs|
    invariant multiset(sorted) == multiset(inputs[..n])
    invariant forall i, j :: 0 <= i < j < |sorted| ==> sorted[i] <= sorted[j]
    decreases |inputs| - n
  {
    var x := inputs[n];
    var prev := sorted;
    assert multiset(prev) == multiset(inputs[..n]);
    var k := 0;

    while k < |prev| && prev[k] <= x
      invariant 0 <= k <= |prev|
      invariant prev == sorted
      invariant forall i, j :: 0 <= i < j < |prev| ==> prev[i] <= prev[j]
      invariant forall i :: 0 <= i < k ==> prev[i] <= x
      decreases |prev| - k
    {
      k := k + 1;
    }

    if k < |prev| {
      assert !(prev[k] <= x);
      assert x <= prev[k] || prev[k] <= x;
      assert x <= prev[k];
    }

    sorted := prev[..k] + [x] + prev[k..];

    forall i, j | 0 <= i < j < |sorted|
      ensures sorted[i] <= sorted[j]
    {
      if j < k {
        assert sorted[i] == prev[i];
        assert sorted[j] == prev[j];
      } else if j == k {
        assert i < k;
        assert sorted[i] == prev[i];
        assert sorted[j] == x;
      } else if i < k {
        assert k < j;
        assert sorted[i] == prev[i];
        assert sorted[j] == prev[j - 1];
        assert 0 <= i < j - 1 < |prev|;
      } else if i == k {
        assert sorted[i] == x;
        assert sorted[j] == prev[j - 1];
        assert k <= j - 1 < |prev|;
        assert k < |prev|;
        assert x <= prev[k];
        if k < j - 1 {
          assert prev[k] <= prev[j - 1];
        }
      } else {
        assert k < i;
        assert sorted[i] == prev[i - 1];
        assert sorted[j] == prev[j - 1];
        assert 0 <= i - 1 < j - 1 < |prev|;
      }
    }

    assert prev == prev[..k] + prev[k..];
    assert sorted == prev[..k] + [x] + prev[k..];
    assert multiset(sorted) == multiset(prev[..k]) + multiset([x]) + multiset(prev[k..]);
    assert multiset(prev) == multiset(prev[..k]) + multiset(prev[k..]);
    assert multiset(sorted) == multiset(prev) + multiset([x]);
    assert x == inputs[n];
    assert multiset(sorted) == multiset(inputs[..n]) + multiset([inputs[n]]);
    assert inputs[..(n + 1)] == inputs[..n] + [inputs[n]];
    assert multiset(inputs[..(n + 1)]) == multiset(inputs[..n]) + multiset([inputs[n]]);
    assert multiset(sorted) == multiset(inputs[..(n + 1)]);

    n := n + 1;
  }

  assert n == |inputs|;
  assert inputs[..n] == inputs;
  assert multiset(inputs) == multiset(sorted);
}