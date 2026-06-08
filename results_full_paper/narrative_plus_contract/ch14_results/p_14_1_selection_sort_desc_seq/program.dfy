method p_14_1_selection_sort_desc_seq(inputs: seq<int>) returns (sorted: seq<int>)
	ensures forall i, j :: 0 <= i < j < |sorted| ==> sorted[i] >= sorted[j]
	ensures multiset(inputs) == multiset(sorted)
{
  var out: seq<int> := [];
  var rest := inputs;

  while |rest| > 0
    invariant multiset(out) + multiset(rest) == multiset(inputs)
    invariant forall i, j :: 0 <= i < j < |out| ==> out[i] >= out[j]
    invariant forall i, j :: 0 <= i < |out| && 0 <= j < |rest| ==> out[i] >= rest[j]
    decreases |rest|
  {
    var m := 0;
    var j := 1;

    while j < |rest|
      invariant 0 < |rest|
      invariant 1 <= j <= |rest|
      invariant 0 <= m < j
      invariant forall k :: 0 <= k < j ==> rest[m] >= rest[k]
      decreases |rest| - j
    {
      if rest[j] > rest[m] {
        var oldM := m;
        m := j;
        assert forall k :: 0 <= k < j ==> rest[m] >= rest[k] by {
          forall k | 0 <= k < j ensures rest[m] >= rest[k] {
            assert rest[oldM] >= rest[k];
            assert rest[m] > rest[oldM];
          }
        }
      }

      assert forall k :: 0 <= k < j + 1 ==> rest[m] >= rest[k] by {
        forall k | 0 <= k < j + 1 ensures rest[m] >= rest[k] {
          if k < j {
            assert rest[m] >= rest[k];
          } else {
            assert k == j;
            assert rest[m] >= rest[k];
          }
        }
      }
      j := j + 1;
    }

    assert forall k :: 0 <= k < |rest| ==> rest[m] >= rest[k];

    var oldOut := out;
    var oldRest := rest;
    var x := oldRest[m];

    out := oldOut + [x];
    rest := oldRest[..m] + oldRest[m + 1..];

    assert oldRest == oldRest[..m] + [oldRest[m]] + oldRest[m + 1..];
    assert x == oldRest[m];
    assert multiset(oldRest) == multiset(oldRest[..m]) + multiset([x]) + multiset(oldRest[m + 1..]);
    assert multiset(rest) == multiset(oldRest[..m]) + multiset(oldRest[m + 1..]);
    assert multiset(out) == multiset(oldOut) + multiset([x]);
    assert multiset(out) + multiset(rest) == multiset(oldOut) + multiset(oldRest);
    assert multiset(out) + multiset(rest) == multiset(inputs);

    assert forall i, j :: 0 <= i < j < |out| ==> out[i] >= out[j] by {
      forall i, j | 0 <= i < j < |out| ensures out[i] >= out[j] {
        if j < |oldOut| {
          assert out[i] == oldOut[i];
          assert out[j] == oldOut[j];
          assert oldOut[i] >= oldOut[j];
        } else {
          assert j == |oldOut|;
          assert i < |oldOut|;
          assert out[i] == oldOut[i];
          assert out[j] == x;
          assert oldOut[i] >= oldRest[m];
        }
      }
    }

    assert forall i, j :: 0 <= i < |out| && 0 <= j < |rest| ==> out[i] >= rest[j] by {
      forall i, j | 0 <= i < |out| && 0 <= j < |rest| ensures out[i] >= rest[j] {
        if i < |oldOut| {
          assert out[i] == oldOut[i];
          if j < m {
            assert rest[j] == oldRest[j];
            assert oldOut[i] >= oldRest[j];
          } else {
            assert j + 1 < |oldRest|;
            assert rest[j] == oldRest[j + 1];
            assert oldOut[i] >= oldRest[j + 1];
          }
        } else {
          assert i == |oldOut|;
          assert out[i] == x;
          if j < m {
            assert rest[j] == oldRest[j];
            assert x >= oldRest[j];
          } else {
            assert j + 1 < |oldRest|;
            assert rest[j] == oldRest[j + 1];
            assert x >= oldRest[j + 1];
          }
        }
      }
    }
  }

  sorted := out;
  assert |rest| == 0;
  assert multiset(rest) == multiset([]);
  assert multiset(sorted) == multiset(inputs);
}