method p_14_2_selection_sort_interval_seq(inputs: seq<int>, bound: nat) returns (sorted: seq<int>)
	requires forall i :: 0 <= i < |inputs| ==> 0 <= inputs[i] <= bound
	ensures forall i, j :: 0 <= i < j < |sorted| ==> sorted[i] <= sorted[j]
	ensures multiset(inputs) == multiset(sorted)
{
  sorted := [];
  var rest := inputs;
  var v: int := 0;

  while v <= bound
    invariant 0 <= v <= bound + 1
    invariant multiset(inputs) == multiset(sorted) + multiset(rest)
    invariant forall i, j :: 0 <= i < j < |sorted| ==> sorted[i] <= sorted[j]
    invariant forall i :: 0 <= i < |sorted| ==> sorted[i] < v
    invariant forall i :: 0 <= i < |rest| ==> v <= rest[i] <= bound
    decreases bound + 1 - v
  {
    assert 0 <= v <= bound;

    while exists k :: 0 <= k < |rest| && rest[k] == v
      invariant 0 <= v <= bound
      invariant multiset(inputs) == multiset(sorted) + multiset(rest)
      invariant forall i, j :: 0 <= i < j < |sorted| ==> sorted[i] <= sorted[j]
      invariant forall i :: 0 <= i < |sorted| ==> sorted[i] <= v
      invariant forall i :: 0 <= i < |rest| ==> v <= rest[i] <= bound
      decreases |rest|
    {
      var k :| 0 <= k < |rest| && rest[k] == v;
      var oldSorted := sorted;
      var oldRest := rest;
      var newSorted := oldSorted + [v];
      var newRest := oldRest[..k] + oldRest[(k + 1)..];

      assert oldRest == oldRest[..k] + [oldRest[k]] + oldRest[(k + 1)..];
      assert oldRest[k] == v;
      assert multiset(oldRest) == multiset([v]) + multiset(newRest);
      assert multiset(newSorted) == multiset(oldSorted) + multiset([v]);
      calc {
        multiset(inputs);
        == multiset(oldSorted) + multiset(oldRest);
        == multiset(oldSorted) + (multiset([v]) + multiset(newRest));
        == (multiset(oldSorted) + multiset([v])) + multiset(newRest);
        == multiset(newSorted) + multiset(newRest);
      }

      assert forall a, b :: 0 <= a < b < |newSorted| ==> newSorted[a] <= newSorted[b] by {
        forall a, b | 0 <= a < b < |newSorted|
          ensures newSorted[a] <= newSorted[b]
        {
          if b < |oldSorted| {
            assert newSorted[a] == oldSorted[a];
            assert newSorted[b] == oldSorted[b];
          } else {
            assert b == |oldSorted|;
            assert a < |oldSorted|;
            assert newSorted[a] == oldSorted[a];
            assert newSorted[b] == v;
            assert oldSorted[a] <= v;
          }
        }
      }

      assert forall t :: 0 <= t < |newSorted| ==> newSorted[t] <= v by {
        forall t | 0 <= t < |newSorted|
          ensures newSorted[t] <= v
        {
          if t < |oldSorted| {
            assert newSorted[t] == oldSorted[t];
          } else {
            assert t == |oldSorted|;
            assert newSorted[t] == v;
          }
        }
      }

      assert forall t :: 0 <= t < |newRest| ==> v <= newRest[t] <= bound by {
        forall t | 0 <= t < |newRest|
          ensures v <= newRest[t] <= bound
        {
          if t < k {
            assert newRest[t] == oldRest[t];
          } else {
            assert t + 1 < |oldRest|;
            assert newRest[t] == oldRest[t + 1];
          }
        }
      }

      sorted := newSorted;
      rest := newRest;
    }

    assert !(exists k :: 0 <= k < |rest| && rest[k] == v);
    assert forall t :: 0 <= t < |rest| ==> v + 1 <= rest[t] <= bound by {
      forall t | 0 <= t < |rest|
        ensures v + 1 <= rest[t] <= bound
      {
        assert v <= rest[t] <= bound;
        assert rest[t] != v;
        assert v < rest[t];
      }
    }
    assert forall t :: 0 <= t < |sorted| ==> sorted[t] < v + 1 by {
      forall t | 0 <= t < |sorted|
        ensures sorted[t] < v + 1
      {
        assert sorted[t] <= v;
      }
    }
    v := v + 1;
  }

  assert v == bound + 1;
  if |rest| != 0 {
    assert 0 <= 0 < |rest|;
    assert v <= rest[0] <= bound;
    assert false;
  }
  assert |rest| == 0;
  assert rest == [];
  assert multiset(rest) == multiset{};
  assert multiset(inputs) == multiset(sorted);
}