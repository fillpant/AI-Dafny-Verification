method p_14_2_selection_sort_interval_seq(inputs: seq<int>, bound: nat) returns (sorted: seq<int>)
	requires forall i :: 0 <= i < |inputs| ==> 0 <= inputs[i] <= bound
	ensures forall i, j :: 0 <= i < j < |sorted| ==> sorted[i] <= sorted[j]
	ensures multiset(inputs) == multiset(sorted)
{
  var rest := inputs;
  sorted := [];

  while |rest| > 0
    invariant multiset(sorted) + multiset(rest) == multiset(inputs)
    invariant forall i, j :: 0 <= i < j < |sorted| ==> sorted[i] <= sorted[j]
    invariant forall i, j :: 0 <= i < |sorted| && 0 <= j < |rest| ==> sorted[i] <= rest[j]
    decreases |rest|
  {
    var minIdx := 0;
    var k := 1;

    while k < |rest|
      invariant 0 <= minIdx < |rest|
      invariant 1 <= k <= |rest|
      invariant forall t :: 0 <= t < k ==> rest[minIdx] <= rest[t]
      decreases |rest| - k
    {
      if rest[k] < rest[minIdx] {
        var oldMinIdx := minIdx;
        minIdx := k;
        forall t | 0 <= t < k
          ensures rest[minIdx] <= rest[t]
        {
          assert rest[minIdx] == rest[k];
          assert rest[k] < rest[oldMinIdx];
          assert rest[oldMinIdx] <= rest[t];
        }
        assert rest[minIdx] <= rest[k];
      } else {
        assert rest[minIdx] <= rest[k];
      }

      forall t | 0 <= t < k + 1
        ensures rest[minIdx] <= rest[t]
      {
        if t < k {
          assert rest[minIdx] <= rest[t];
        } else {
          assert t == k;
          assert rest[minIdx] <= rest[k];
        }
      }
      k := k + 1;
    }

    assert k == |rest|;
    assert forall t :: 0 <= t < |rest| ==> rest[minIdx] <= rest[t];

    var oldSorted := sorted;
    var oldRest := rest;
    var m := oldRest[minIdx];

    assert forall i, j :: 0 <= i < j < |oldSorted| ==> oldSorted[i] <= oldSorted[j];
    assert forall i, j :: 0 <= i < |oldSorted| && 0 <= j < |oldRest| ==> oldSorted[i] <= oldRest[j];
    assert multiset(oldSorted) + multiset(oldRest) == multiset(inputs);

    forall t | 0 <= t < |oldRest|
      ensures m <= oldRest[t]
    {
      assert oldRest[t] == rest[t];
      assert m == rest[minIdx];
      assert rest[minIdx] <= rest[t];
    }

    assert oldRest[minIdx..minIdx + 1] == [m];
    assert oldRest[minIdx..] == [m] + oldRest[minIdx + 1..];
    assert oldRest == oldRest[..minIdx] + oldRest[minIdx..];
    assert oldRest == oldRest[..minIdx] + [m] + oldRest[minIdx + 1..];

    sorted := oldSorted + [m];
    rest := oldRest[..minIdx] + oldRest[minIdx + 1..];

    assert |sorted| == |oldSorted| + 1;
    assert |rest| == |oldRest| - 1;
    assert |rest| < |oldRest|;

    forall i, j | 0 <= i < j < |sorted|
      ensures sorted[i] <= sorted[j]
    {
      if j < |oldSorted| {
        assert sorted[i] == oldSorted[i];
        assert sorted[j] == oldSorted[j];
        assert oldSorted[i] <= oldSorted[j];
      } else {
        assert j == |oldSorted|;
        assert i < |oldSorted|;
        assert sorted[i] == oldSorted[i];
        assert sorted[j] == m;
        assert oldSorted[i] <= oldRest[minIdx];
      }
    }

    forall i, j | 0 <= i < |sorted| && 0 <= j < |rest|
      ensures sorted[i] <= rest[j]
    {
      if j < minIdx {
        assert rest[j] == oldRest[j];
        if i < |oldSorted| {
          assert sorted[i] == oldSorted[i];
          assert oldSorted[i] <= oldRest[j];
        } else {
          assert i == |oldSorted|;
          assert sorted[i] == m;
          assert m <= oldRest[j];
        }
      } else {
        assert minIdx <= j;
        assert j + 1 < |oldRest|;
        assert rest[j] == oldRest[j + 1];
        if i < |oldSorted| {
          assert sorted[i] == oldSorted[i];
          assert oldSorted[i] <= oldRest[j + 1];
        } else {
          assert i == |oldSorted|;
          assert sorted[i] == m;
          assert m <= oldRest[j + 1];
        }
      }
    }

    assert multiset(oldRest) == multiset(oldRest[..minIdx]) + multiset([m]) + multiset(oldRest[minIdx + 1..]);
    assert multiset(sorted) == multiset(oldSorted) + multiset([m]);
    assert multiset(rest) == multiset(oldRest[..minIdx]) + multiset(oldRest[minIdx + 1..]);

    calc {
      multiset(sorted) + multiset(rest);
    ==
      (multiset(oldSorted) + multiset([m])) + (multiset(oldRest[..minIdx]) + multiset(oldRest[minIdx + 1..]));
    ==
      multiset(oldSorted) + multiset(oldRest);
    ==
      multiset(inputs);
    }
  }

  assert rest == [];
  assert multiset(rest) == multiset([]);
  assert multiset(sorted) + multiset(rest) == multiset(sorted);
  assert multiset(sorted) == multiset(inputs);
  assert multiset(inputs) == multiset(sorted);
}