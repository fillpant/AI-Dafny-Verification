method p_14_4_merge_sort_lexicographic_array(inputs: array<string>) returns (sorted: array<string>)
	ensures forall i, j :: 0 <= i < j < sorted.Length ==> sorted[i] <= sorted[j]
	ensures multiset(inputs[..]) == multiset(sorted[..])
{
  var out: seq<string> := [];
  var rem: seq<string> := inputs[..];

  while |rem| > 0
    invariant multiset(out) + multiset(rem) == multiset(inputs[..])
    invariant forall i, j :: 0 <= i < j < |out| ==> out[i] <= out[j]
    invariant forall i, j :: 0 <= i < |out| && 0 <= j < |rem| ==> out[i] <= rem[j]
    decreases |rem|
  {
    var min := 0;
    var k := 1;

    while k < |rem|
      invariant 0 <= min < |rem|
      invariant 1 <= k <= |rem|
      invariant min < k
      invariant forall t :: 0 <= t < k ==> rem[min] <= rem[t]
      decreases |rem| - k
    {
      if rem[min] <= rem[k] {
        assert rem[min] <= rem[k];
      } else {
        var oldMin := min;
        assert rem[k] <= rem[oldMin] || rem[oldMin] <= rem[k];
        assert rem[k] <= rem[oldMin];
        min := k;
        forall t | 0 <= t < k
          ensures rem[min] <= rem[t]
        {
          assert rem[min] <= rem[oldMin];
          assert rem[oldMin] <= rem[t];
        }
      }
      forall t | 0 <= t < k + 1
        ensures rem[min] <= rem[t]
      {
        if t < k {
          assert rem[min] <= rem[t];
        } else {
          assert t == k;
          assert rem[min] <= rem[k];
        }
      }
      k := k + 1;
    }

    var m := rem[min];
    var oldOut := out;
    var oldRem := rem;
    var newRem := oldRem[..min] + oldRem[min + 1..];

    assert forall t :: 0 <= t < |oldRem| ==> m <= oldRem[t];
    assert forall i :: 0 <= i < |oldOut| ==> oldOut[i] <= m;

    assert oldRem == oldRem[..min] + [m] + oldRem[min + 1..];
    assert multiset(oldRem) == multiset(oldRem[..min]) + multiset([m]) + multiset(oldRem[min + 1..]);
    assert multiset(newRem) == multiset(oldRem[..min]) + multiset(oldRem[min + 1..]);
    assert multiset([m]) + multiset(newRem) == multiset(oldRem);

    out := oldOut + [m];
    rem := newRem;

    assert multiset(out) == multiset(oldOut) + multiset([m]);
    assert multiset(rem) == multiset(newRem);
    assert multiset(out) + multiset(rem) == multiset(oldOut) + multiset(oldRem);
    assert |out| == |oldOut| + 1;

    forall i, j | 0 <= i < j < |out|
      ensures out[i] <= out[j]
    {
      if j < |oldOut| {
        assert out[i] == oldOut[i];
        assert out[j] == oldOut[j];
        assert oldOut[i] <= oldOut[j];
      } else {
        assert j == |oldOut|;
        assert i < |oldOut|;
        assert out[i] == oldOut[i];
        assert out[j] == m;
        assert oldOut[i] <= m;
      }
    }

    assert |rem| == |oldRem| - 1;
    assert forall j :: 0 <= j < |rem| && j < min ==> rem[j] == oldRem[j];
    assert forall j :: 0 <= j < |rem| && min <= j ==> rem[j] == oldRem[j + 1];

    forall i, j | 0 <= i < |out| && 0 <= j < |rem|
      ensures out[i] <= rem[j]
    {
      if j < min {
        assert rem[j] == oldRem[j];
        if i < |oldOut| {
          assert out[i] == oldOut[i];
          assert oldOut[i] <= oldRem[j];
        } else {
          assert i == |oldOut|;
          assert out[i] == m;
          assert m <= oldRem[j];
        }
      } else {
        assert rem[j] == oldRem[j + 1];
        assert 0 <= j + 1 < |oldRem|;
        if i < |oldOut| {
          assert out[i] == oldOut[i];
          assert oldOut[i] <= oldRem[j + 1];
        } else {
          assert i == |oldOut|;
          assert out[i] == m;
          assert m <= oldRem[j + 1];
        }
      }
    }
  }

  assert rem == [];
  assert multiset(out) == multiset(inputs[..]);

  sorted := new string[|out|];
  var idx := 0;
  while idx < |out|
    invariant sorted.Length == |out|
    invariant 0 <= idx <= |out|
    invariant forall i :: 0 <= i < idx ==> sorted[i] == out[i]
    decreases |out| - idx
  {
    sorted[idx] := out[idx];
    idx := idx + 1;
  }

  assert sorted.Length == |out|;
  assert forall i :: 0 <= i < sorted.Length ==> sorted[i] == out[i];
  assert |sorted[..]| == |out|;
  assert forall i :: 0 <= i < |out| ==> sorted[..][i] == out[i];
  assert sorted[..] == out;

  forall i, j | 0 <= i < j < sorted.Length
    ensures sorted[i] <= sorted[j]
  {
    assert sorted[i] == out[i];
    assert sorted[j] == out[j];
    assert out[i] <= out[j];
  }
  assert multiset(sorted[..]) == multiset(out);
}