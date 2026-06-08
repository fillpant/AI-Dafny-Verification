method p_14_4_bubble_sort_seq(inputs: seq<int>) returns (sorted: seq<int>)
	ensures forall i, j :: 0 <= i < j < |sorted| ==> sorted[i] <= sorted[j]
	ensures multiset(inputs) == multiset(sorted)
{
  sorted := [];
  var rest := inputs;

  while |rest| > 0
    invariant forall i, j :: 0 <= i < j < |sorted| ==> sorted[i] <= sorted[j]
    invariant forall i, j :: 0 <= i < |sorted| && 0 <= j < |rest| ==> sorted[i] <= rest[j]
    invariant multiset(inputs) == multiset(sorted) + multiset(rest)
    decreases |rest|
  {
    assert 0 < |rest|;
    var minIdx := 0;
    var scan := 1;
    assert forall t :: 0 <= t < 1 ==> rest[0] <= rest[t];

    while scan < |rest|
      invariant 0 <= minIdx < |rest|
      invariant 1 <= scan <= |rest|
      invariant minIdx < scan
      invariant forall t :: 0 <= t < scan ==> rest[minIdx] <= rest[t]
      decreases |rest| - scan
    {
      var prevMin := minIdx;
      if rest[scan] < rest[prevMin] {
        minIdx := scan;
        assert forall t :: 0 <= t < scan ==> rest[minIdx] <= rest[t] by {
          forall t | 0 <= t < scan
            ensures rest[minIdx] <= rest[t]
          {
            assert rest[prevMin] <= rest[t];
            assert rest[minIdx] == rest[scan];
            assert rest[scan] < rest[prevMin];
          }
        }
      } else {
        assert minIdx == prevMin;
        assert rest[minIdx] <= rest[scan];
      }

      assert forall t :: 0 <= t < scan + 1 ==> rest[minIdx] <= rest[t] by {
        forall t | 0 <= t < scan + 1
          ensures rest[minIdx] <= rest[t]
        {
          if t < scan {
            assert rest[minIdx] <= rest[t];
          } else {
            assert t == scan;
            assert rest[minIdx] <= rest[scan];
          }
        }
      }
      scan := scan + 1;
    }

    assert scan == |rest|;
    var m := rest[minIdx];
    assert forall t :: 0 <= t < |rest| ==> m <= rest[t];

    var priorSorted := sorted;
    var priorRest := rest;
    ghost var priorSortedLen := |priorSorted|;
    ghost var priorRestLen := |priorRest|;

    sorted := priorSorted + [m];
    rest := priorRest[..minIdx] + priorRest[minIdx + 1..];

    assert |sorted| == priorSortedLen + 1;
    assert |rest| == priorRestLen - 1;

    assert forall i, j :: 0 <= i < j < |sorted| ==> sorted[i] <= sorted[j] by {
      forall i, j | 0 <= i < j < |sorted|
        ensures sorted[i] <= sorted[j]
      {
        if j < priorSortedLen {
          assert sorted[i] == priorSorted[i];
          assert sorted[j] == priorSorted[j];
          assert priorSorted[i] <= priorSorted[j];
        } else {
          assert j == priorSortedLen;
          assert i < priorSortedLen;
          assert sorted[i] == priorSorted[i];
          assert sorted[j] == m;
          assert priorSorted[i] <= priorRest[minIdx];
        }
      }
    }

    assert forall i, j :: 0 <= i < |sorted| && 0 <= j < |rest| ==> sorted[i] <= rest[j] by {
      forall i, j | 0 <= i < |sorted| && 0 <= j < |rest|
        ensures sorted[i] <= rest[j]
      {
        if j < minIdx {
          assert rest[j] == priorRest[j];
          if i < priorSortedLen {
            assert sorted[i] == priorSorted[i];
            assert priorSorted[i] <= priorRest[j];
          } else {
            assert i == priorSortedLen;
            assert sorted[i] == m;
            assert m <= priorRest[j];
          }
        } else {
          assert j + 1 < priorRestLen;
          assert rest[j] == priorRest[j + 1];
          if i < priorSortedLen {
            assert sorted[i] == priorSorted[i];
            assert priorSorted[i] <= priorRest[j + 1];
          } else {
            assert i == priorSortedLen;
            assert sorted[i] == m;
            assert m <= priorRest[j + 1];
          }
        }
      }
    }

    assert priorRest == priorRest[..minIdx] + [m] + priorRest[minIdx + 1..];
    assert multiset(priorRest) == multiset(priorRest[..minIdx]) + multiset([m]) + multiset(priorRest[minIdx + 1..]);
    assert multiset(rest) == multiset(priorRest[..minIdx]) + multiset(priorRest[minIdx + 1..]);
    assert multiset(priorRest) == multiset(rest) + multiset([m]);
    assert multiset(sorted) == multiset(priorSorted) + multiset([m]);
    assert multiset(inputs) == multiset(priorSorted) + multiset(priorRest);
    assert multiset(sorted) + multiset(rest) == multiset(inputs);
    assert multiset(inputs) == multiset(sorted) + multiset(rest);
  }

  assert |rest| == 0;
  assert rest == [];
  assert multiset(inputs) == multiset(sorted) + multiset(rest);
  assert multiset(inputs) == multiset(sorted);
}