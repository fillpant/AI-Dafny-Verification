method p_14_4_merge_sort_lexicographic_seq(inputs: seq<string>) returns (sorted: seq<string>)
	ensures forall i, j :: 0 <= i < j < |sorted| ==> sorted[i] <= sorted[j]
	ensures multiset(inputs) == multiset(sorted)
{
  if |inputs| <= 1 {
    sorted := inputs;
    return;
  }

  var mid := |inputs| / 2;
  assert 0 < mid < |inputs|;
  assert inputs == inputs[..mid] + inputs[mid..];

  var left := p_14_4_merge_sort_lexicographic_seq(inputs[..mid]);
  var right := p_14_4_merge_sort_lexicographic_seq(inputs[mid..]);

  var i := 0;
  var j := 0;
  sorted := [];

  while i < |left| || j < |right|
    invariant 0 <= i <= |left|
    invariant 0 <= j <= |right|
    invariant forall a, b :: 0 <= a < b < |sorted| ==> sorted[a] <= sorted[b]
    invariant multiset(sorted) == multiset(left[..i]) + multiset(right[..j])
    invariant forall k :: i <= k < |left| ==> |sorted| == 0 || sorted[|sorted|-1] <= left[k]
    invariant forall k :: j <= k < |right| ==> |sorted| == 0 || sorted[|sorted|-1] <= right[k]
    decreases |left| - i + |right| - j
  {
    if i < |left| && (j == |right| || !(right[j] < left[i])) {
      var oldSorted := sorted;
      var oldI := i;
      var x := left[oldI];

      if j < |right| {
        assert !(right[j] < x);
        assert x <= right[j];
      }

      forall a | 0 <= a < |oldSorted|
        ensures oldSorted[a] <= x
      {
        if |oldSorted| > 0 {
          assert oldSorted[|oldSorted|-1] <= x;
          if a < |oldSorted| - 1 {
            assert oldSorted[a] <= oldSorted[|oldSorted|-1];
          }
        }
      }

      sorted := oldSorted + [x];
      i := oldI + 1;

      assert left[..i] == left[..oldI] + [x];
      assert multiset(sorted) == multiset(oldSorted) + multiset([x]);
      assert multiset(left[..i]) == multiset(left[..oldI]) + multiset([x]);

      forall a, b | 0 <= a < b < |sorted|
        ensures sorted[a] <= sorted[b]
      {
        if b < |oldSorted| {
          assert sorted[a] == oldSorted[a];
          assert sorted[b] == oldSorted[b];
        } else {
          assert b == |oldSorted|;
          assert sorted[b] == x;
          assert oldSorted[a] <= x;
        }
      }

      forall k | i <= k < |left|
        ensures sorted[|sorted|-1] <= left[k]
      {
        assert sorted[|sorted|-1] == x;
        assert oldI < k;
        assert left[oldI] <= left[k];
      }

      forall k | j <= k < |right|
        ensures sorted[|sorted|-1] <= right[k]
      {
        assert sorted[|sorted|-1] == x;
        if j < |right| {
          assert x <= right[j];
          if j < k {
            assert right[j] <= right[k];
          }
        }
      }
    } else {
      assert j < |right|;
      var oldSorted := sorted;
      var oldJ := j;
      var x := right[oldJ];

      if i < |left| {
        assert right[oldJ] < left[i];
        assert right[oldJ] <= left[i];
      }

      forall a | 0 <= a < |oldSorted|
        ensures oldSorted[a] <= x
      {
        if |oldSorted| > 0 {
          assert oldSorted[|oldSorted|-1] <= x;
          if a < |oldSorted| - 1 {
            assert oldSorted[a] <= oldSorted[|oldSorted|-1];
          }
        }
      }

      sorted := oldSorted + [x];
      j := oldJ + 1;

      assert right[..j] == right[..oldJ] + [x];
      assert multiset(sorted) == multiset(oldSorted) + multiset([x]);
      assert multiset(right[..j]) == multiset(right[..oldJ]) + multiset([x]);

      forall a, b | 0 <= a < b < |sorted|
        ensures sorted[a] <= sorted[b]
      {
        if b < |oldSorted| {
          assert sorted[a] == oldSorted[a];
          assert sorted[b] == oldSorted[b];
        } else {
          assert b == |oldSorted|;
          assert sorted[b] == x;
          assert oldSorted[a] <= x;
        }
      }

      forall k | j <= k < |right|
        ensures sorted[|sorted|-1] <= right[k]
      {
        assert sorted[|sorted|-1] == x;
        assert oldJ < k;
        assert right[oldJ] <= right[k];
      }

      forall k | i <= k < |left|
        ensures sorted[|sorted|-1] <= left[k]
      {
        assert sorted[|sorted|-1] == x;
        if i < |left| {
          assert x <= left[i];
          if i < k {
            assert left[i] <= left[k];
          }
        }
      }
    }
  }

  assert i == |left|;
  assert j == |right|;
  assert left[..i] == left;
  assert right[..j] == right;
  assert multiset(sorted) == multiset(left) + multiset(right);
  assert multiset(inputs) == multiset(inputs[..mid]) + multiset(inputs[mid..]);
  assert multiset(inputs[..mid]) == multiset(left);
  assert multiset(inputs[mid..]) == multiset(right);
  assert multiset(inputs) == multiset(sorted);
}