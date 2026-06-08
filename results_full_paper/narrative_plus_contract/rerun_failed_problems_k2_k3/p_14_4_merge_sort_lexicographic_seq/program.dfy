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
  assert |inputs[..mid]| < |inputs|;
  assert |inputs[mid..]| < |inputs|;

  var left := p_14_4_merge_sort_lexicographic_seq(inputs[..mid]);
  var right := p_14_4_merge_sort_lexicographic_seq(inputs[mid..]);

  sorted := [];
  var i := 0;
  var j := 0;

  while i < |left| || j < |right|
    invariant 0 <= i <= |left|
    invariant 0 <= j <= |right|
    invariant |sorted| == i + j
    invariant forall a, b :: 0 <= a < b < |sorted| ==> sorted[a] <= sorted[b]
    invariant multiset(sorted) == multiset(left[..i]) + multiset(right[..j])
    invariant forall a :: 0 <= a < |sorted| && i < |left| ==> sorted[a] <= left[i]
    invariant forall a :: 0 <= a < |sorted| && j < |right| ==> sorted[a] <= right[j]
    decreases |left| + |right| - i - j
  {
    if i == |left| {
      assert j < |right|;
      var oldSorted := sorted;
      var oldJ := j;
      assert forall a, b :: 0 <= a < b < |oldSorted| ==> oldSorted[a] <= oldSorted[b];
      assert forall a :: 0 <= a < |oldSorted| ==> oldSorted[a] <= right[oldJ];

      sorted := oldSorted + [right[oldJ]];
      j := oldJ + 1;

      forall a, b | 0 <= a < b < |sorted|
        ensures sorted[a] <= sorted[b]
      {
        if b < |oldSorted| {
          assert sorted[a] == oldSorted[a];
          assert sorted[b] == oldSorted[b];
          assert oldSorted[a] <= oldSorted[b];
        } else {
          assert b == |oldSorted|;
          assert a < |oldSorted|;
          assert sorted[a] == oldSorted[a];
          assert sorted[b] == right[oldJ];
          assert oldSorted[a] <= right[oldJ];
        }
      }
      assert right[..j] == right[..oldJ] + [right[oldJ]];
      assert multiset(sorted) == multiset(left[..i]) + multiset(right[..j]);
      assert forall a :: 0 <= a < |sorted| && i < |left| ==> sorted[a] <= left[i];
      forall a | 0 <= a < |sorted| && j < |right|
        ensures sorted[a] <= right[j]
      {
        assert oldJ + 1 < |right|;
        assert right[oldJ] <= right[j];
        if a < |oldSorted| {
          assert sorted[a] == oldSorted[a];
          assert oldSorted[a] <= right[oldJ];
        } else {
          assert a == |oldSorted|;
          assert sorted[a] == right[oldJ];
        }
      }
    } else if j == |right| {
      assert i < |left|;
      var oldSorted := sorted;
      var oldI := i;
      assert forall a, b :: 0 <= a < b < |oldSorted| ==> oldSorted[a] <= oldSorted[b];
      assert forall a :: 0 <= a < |oldSorted| ==> oldSorted[a] <= left[oldI];

      sorted := oldSorted + [left[oldI]];
      i := oldI + 1;

      forall a, b | 0 <= a < b < |sorted|
        ensures sorted[a] <= sorted[b]
      {
        if b < |oldSorted| {
          assert sorted[a] == oldSorted[a];
          assert sorted[b] == oldSorted[b];
          assert oldSorted[a] <= oldSorted[b];
        } else {
          assert b == |oldSorted|;
          assert a < |oldSorted|;
          assert sorted[a] == oldSorted[a];
          assert sorted[b] == left[oldI];
          assert oldSorted[a] <= left[oldI];
        }
      }
      assert left[..i] == left[..oldI] + [left[oldI]];
      assert multiset(sorted) == multiset(left[..i]) + multiset(right[..j]);
      forall a | 0 <= a < |sorted| && i < |left|
        ensures sorted[a] <= left[i]
      {
        assert oldI + 1 < |left|;
        assert left[oldI] <= left[i];
        if a < |oldSorted| {
          assert sorted[a] == oldSorted[a];
          assert oldSorted[a] <= left[oldI];
        } else {
          assert a == |oldSorted|;
          assert sorted[a] == left[oldI];
        }
      }
      assert forall a :: 0 <= a < |sorted| && j < |right| ==> sorted[a] <= right[j];
    } else if left[i] <= right[j] {
      assert i < |left| && j < |right|;
      var oldSorted := sorted;
      var oldI := i;
      var oldJ := j;
      assert forall a, b :: 0 <= a < b < |oldSorted| ==> oldSorted[a] <= oldSorted[b];
      assert forall a :: 0 <= a < |oldSorted| ==> oldSorted[a] <= left[oldI];
      assert forall a :: 0 <= a < |oldSorted| ==> oldSorted[a] <= right[oldJ];
      assert left[oldI] <= right[oldJ];

      sorted := oldSorted + [left[oldI]];
      i := oldI + 1;

      forall a, b | 0 <= a < b < |sorted|
        ensures sorted[a] <= sorted[b]
      {
        if b < |oldSorted| {
          assert sorted[a] == oldSorted[a];
          assert sorted[b] == oldSorted[b];
          assert oldSorted[a] <= oldSorted[b];
        } else {
          assert b == |oldSorted|;
          assert a < |oldSorted|;
          assert sorted[a] == oldSorted[a];
          assert sorted[b] == left[oldI];
          assert oldSorted[a] <= left[oldI];
        }
      }
      assert left[..i] == left[..oldI] + [left[oldI]];
      assert multiset(sorted) == multiset(left[..i]) + multiset(right[..j]);
      forall a | 0 <= a < |sorted| && i < |left|
        ensures sorted[a] <= left[i]
      {
        assert oldI + 1 < |left|;
        assert left[oldI] <= left[i];
        if a < |oldSorted| {
          assert sorted[a] == oldSorted[a];
          assert oldSorted[a] <= left[oldI];
        } else {
          assert a == |oldSorted|;
          assert sorted[a] == left[oldI];
        }
      }
      forall a | 0 <= a < |sorted| && j < |right|
        ensures sorted[a] <= right[j]
      {
        assert j == oldJ;
        if a < |oldSorted| {
          assert sorted[a] == oldSorted[a];
          assert oldSorted[a] <= right[oldJ];
        } else {
          assert a == |oldSorted|;
          assert sorted[a] == left[oldI];
          assert left[oldI] <= right[oldJ];
        }
      }
    } else {
      assert i < |left| && j < |right|;
      assert right[j] <= left[i];
      var oldSorted := sorted;
      var oldI := i;
      var oldJ := j;
      assert forall a, b :: 0 <= a < b < |oldSorted| ==> oldSorted[a] <= oldSorted[b];
      assert forall a :: 0 <= a < |oldSorted| ==> oldSorted[a] <= left[oldI];
      assert forall a :: 0 <= a < |oldSorted| ==> oldSorted[a] <= right[oldJ];
      assert right[oldJ] <= left[oldI];

      sorted := oldSorted + [right[oldJ]];
      j := oldJ + 1;

      forall a, b | 0 <= a < b < |sorted|
        ensures sorted[a] <= sorted[b]
      {
        if b < |oldSorted| {
          assert sorted[a] == oldSorted[a];
          assert sorted[b] == oldSorted[b];
          assert oldSorted[a] <= oldSorted[b];
        } else {
          assert b == |oldSorted|;
          assert a < |oldSorted|;
          assert sorted[a] == oldSorted[a];
          assert sorted[b] == right[oldJ];
          assert oldSorted[a] <= right[oldJ];
        }
      }
      assert right[..j] == right[..oldJ] + [right[oldJ]];
      assert multiset(sorted) == multiset(left[..i]) + multiset(right[..j]);
      forall a | 0 <= a < |sorted| && i < |left|
        ensures sorted[a] <= left[i]
      {
        assert i == oldI;
        if a < |oldSorted| {
          assert sorted[a] == oldSorted[a];
          assert oldSorted[a] <= left[oldI];
        } else {
          assert a == |oldSorted|;
          assert sorted[a] == right[oldJ];
          assert right[oldJ] <= left[oldI];
        }
      }
      forall a | 0 <= a < |sorted| && j < |right|
        ensures sorted[a] <= right[j]
      {
        assert oldJ + 1 < |right|;
        assert right[oldJ] <= right[j];
        if a < |oldSorted| {
          assert sorted[a] == oldSorted[a];
          assert oldSorted[a] <= right[oldJ];
        } else {
          assert a == |oldSorted|;
          assert sorted[a] == right[oldJ];
        }
      }
    }
  }

  assert i == |left|;
  assert j == |right|;
  assert left[..i] == left;
  assert right[..j] == right;
  assert multiset(sorted) == multiset(left) + multiset(right);
  assert inputs == inputs[..mid] + inputs[mid..];
  assert multiset(inputs) == multiset(inputs[..mid]) + multiset(inputs[mid..]);
  assert multiset(left) == multiset(inputs[..mid]);
  assert multiset(right) == multiset(inputs[mid..]);
  assert multiset(inputs) == multiset(sorted);
}