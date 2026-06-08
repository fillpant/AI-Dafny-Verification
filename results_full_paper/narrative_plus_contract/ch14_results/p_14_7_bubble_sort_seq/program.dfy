method p_14_4_bubble_sort_seq(inputs: seq<int>) returns (sorted: seq<int>)
	ensures forall i, j :: 0 <= i < j < |sorted| ==> sorted[i] <= sorted[j]
	ensures multiset(inputs) == multiset(sorted)
{
  sorted := inputs;
  var n := |sorted|;

  while n > 0
    invariant 0 <= n <= |sorted|
    invariant multiset(sorted) == multiset(inputs)
    invariant forall a, b :: n <= a < b < |sorted| ==> sorted[a] <= sorted[b]
    invariant forall a, b :: 0 <= a < n <= b < |sorted| ==> sorted[a] <= sorted[b]
    decreases n
  {
    var j := 0;

    while j + 1 < n
      invariant 0 <= j < n <= |sorted|
      invariant multiset(sorted) == multiset(inputs)
      invariant forall a, b :: n <= a < b < |sorted| ==> sorted[a] <= sorted[b]
      invariant forall a, b :: 0 <= a < n <= b < |sorted| ==> sorted[a] <= sorted[b]
      invariant forall k :: 0 <= k < j ==> sorted[k] <= sorted[j]
      decreases n - j
    {
      var before := sorted;
      var doSwap := before[j] > before[j + 1];

      if doSwap {
        assert 0 <= j < j + 1 < |before|;
        assert before == before[..j] + [before[j], before[j + 1]] + before[j + 2..];
        sorted := before[..j] + [before[j + 1], before[j]] + before[j + 2..];
        assert |sorted| == |before|;
        assert sorted[j] == before[j + 1];
        assert sorted[j + 1] == before[j];
        assert forall k :: 0 <= k < |sorted| && k != j && k != j + 1 ==> sorted[k] == before[k];
        assert multiset(sorted) == multiset(before[..j]) + multiset([before[j + 1], before[j]]) + multiset(before[j + 2..]);
        assert multiset(before) == multiset(before[..j]) + multiset([before[j], before[j + 1]]) + multiset(before[j + 2..]);
        assert multiset([before[j + 1], before[j]]) == multiset([before[j], before[j + 1]]);
        assert multiset(sorted) == multiset(before);
      } else {
        assert sorted == before;
      }

      assert |sorted| == |before|;
      assert multiset(sorted) == multiset(inputs);

      forall a, b | n <= a < b < |sorted|
        ensures sorted[a] <= sorted[b]
      {
        assert j + 1 < n <= a;
        if doSwap {
          assert sorted[a] == before[a];
          assert sorted[b] == before[b];
        } else {
          assert sorted == before;
        }
        assert before[a] <= before[b];
      }

      forall a, b | 0 <= a < n <= b < |sorted|
        ensures sorted[a] <= sorted[b]
      {
        assert j + 1 < n <= b;
        if doSwap {
          assert sorted[b] == before[b];
          if a == j {
            assert sorted[a] == before[j + 1];
            assert 0 <= j + 1 < n <= b < |before|;
            assert before[j + 1] <= before[b];
          } else if a == j + 1 {
            assert sorted[a] == before[j];
            assert 0 <= j < n <= b < |before|;
            assert before[j] <= before[b];
          } else {
            assert sorted[a] == before[a];
            assert 0 <= a < n <= b < |before|;
            assert before[a] <= before[b];
          }
        } else {
          assert sorted == before;
          assert before[a] <= before[b];
        }
      }

      forall k | 0 <= k < j + 1
        ensures sorted[k] <= sorted[j + 1]
      {
        if doSwap {
          assert sorted[j + 1] == before[j];
          if k == j {
            assert sorted[k] == before[j + 1];
            assert before[j + 1] <= before[j];
          } else {
            assert k < j;
            assert before[k] <= before[j];
            assert sorted[k] == before[k];
          }
        } else {
          assert sorted == before;
          assert before[j] <= before[j + 1];
          if k == j {
            assert before[k] <= before[j + 1];
          } else {
            assert k < j;
            assert before[k] <= before[j];
            assert before[k] <= before[j + 1];
          }
        }
      }

      j := j + 1;
    }

    var oldN := n;
    assert j + 1 >= oldN;
    assert j == oldN - 1;
    var newN := oldN - 1;
    assert 0 <= newN;

    forall a, b | newN <= a < b < |sorted|
      ensures sorted[a] <= sorted[b]
    {
      if a == newN {
        assert b >= oldN;
        assert 0 <= a < oldN <= b < |sorted|;
        assert sorted[a] <= sorted[b];
      } else {
        assert oldN <= a < b < |sorted|;
        assert sorted[a] <= sorted[b];
      }
    }

    forall a, b | 0 <= a < newN <= b < |sorted|
      ensures sorted[a] <= sorted[b]
    {
      if b == newN {
        assert a < j;
        assert sorted[a] <= sorted[j];
        assert j == newN;
      } else {
        assert b >= oldN;
        assert 0 <= a < oldN <= b < |sorted|;
        assert sorted[a] <= sorted[b];
      }
    }

    n := newN;
  }
}