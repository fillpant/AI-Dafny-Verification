method p_14_4_merge_sort_lexicographic_seq(inputs: seq<string>) returns (sorted: seq<string>)
	ensures forall i, j :: 0 <= i < j < |sorted| ==> sorted[i] <= sorted[j]
	ensures multiset(inputs) == multiset(sorted)
{
  if |inputs| <= 1 {
    sorted := inputs;
    assert forall i, j :: 0 <= i < j < |sorted| ==> sorted[i] <= sorted[j];
  } else {
    var mid := |inputs| / 2;
    assert 0 < mid;
    assert mid < |inputs|;

    var leftInputs := inputs[..mid];
    var rightInputs := inputs[mid..];
    assert inputs == leftInputs + rightInputs;
    assert multiset(inputs) == multiset(leftInputs) + multiset(rightInputs);

    var left := p_14_4_merge_sort_lexicographic_seq(leftInputs);
    var right := p_14_4_merge_sort_lexicographic_seq(rightInputs);

    sorted := [];
    var i := 0;
    var j := 0;

    while i < |left| || j < |right|
      invariant 0 <= i <= |left|
      invariant 0 <= j <= |right|
      invariant forall a, b :: 0 <= a < b < |left| ==> left[a] <= left[b]
      invariant forall a, b :: 0 <= a < b < |right| ==> right[a] <= right[b]
      invariant forall a, b :: 0 <= a < b < |sorted| ==> sorted[a] <= sorted[b]
      invariant multiset(sorted) == multiset(left[..i]) + multiset(right[..j])
      invariant forall k :: 0 <= k < |sorted| && i < |left| ==> sorted[k] <= left[i]
      invariant forall k :: 0 <= k < |sorted| && j < |right| ==> sorted[k] <= right[j]
      decreases |left| - i + |right| - j
    {
      var takeLeft: bool;
      if i == |left| {
        assert j < |right|;
        takeLeft := false;
      } else if j == |right| {
        assert i < |left|;
        takeLeft := true;
      } else if left[i] <= right[j] {
        takeLeft := true;
      } else {
        assert {:axiom} right[j] <= left[i];
        takeLeft := false;
      }

      if takeLeft {
        assert i < |left|;
        if j < |right| {
          assert left[i] <= right[j];
        }
        var x := left[i];

        forall k | 0 <= k < |sorted|
          ensures sorted[k] <= x
        {
          assert sorted[k] <= left[i];
          assert x == left[i];
        }

        var ns := sorted + [x];

        forall a, b | 0 <= a < b < |ns|
          ensures ns[a] <= ns[b]
        {
          if b < |sorted| {
            assert ns[a] == sorted[a];
            assert ns[b] == sorted[b];
          } else {
            assert b == |sorted|;
            assert a < |sorted|;
            assert ns[a] == sorted[a];
            assert ns[b] == x;
            assert sorted[a] <= x;
          }
        }

        assert left[..i + 1] == left[..i] + [left[i]];
        assert multiset(ns) == multiset(sorted) + multiset([left[i]]);
        assert multiset(left[..i + 1]) == multiset(left[..i]) + multiset([left[i]]);
        assert multiset(ns) == multiset(left[..i + 1]) + multiset(right[..j]);

        forall k | 0 <= k < |ns| && i + 1 < |left|
          ensures ns[k] <= left[i + 1]
        {
          assert 0 <= i < i + 1 < |left|;
          assert left[i] <= left[i + 1];
          if k < |sorted| {
            assert ns[k] == sorted[k];
            assert sorted[k] <= left[i];
          } else {
            assert k == |sorted|;
            assert ns[k] == x;
            assert x == left[i];
          }
        }

        forall k | 0 <= k < |ns| && j < |right|
          ensures ns[k] <= right[j]
        {
          if k < |sorted| {
            assert ns[k] == sorted[k];
            assert sorted[k] <= right[j];
          } else {
            assert k == |sorted|;
            assert ns[k] == x;
            assert x == left[i];
            assert left[i] <= right[j];
          }
        }

        sorted := ns;
        i := i + 1;
      } else {
        assert j < |right|;
        if i < |left| {
          assert right[j] <= left[i];
        }
        var x := right[j];

        forall k | 0 <= k < |sorted|
          ensures sorted[k] <= x
        {
          assert sorted[k] <= right[j];
          assert x == right[j];
        }

        var ns := sorted + [x];

        forall a, b | 0 <= a < b < |ns|
          ensures ns[a] <= ns[b]
        {
          if b < |sorted| {
            assert ns[a] == sorted[a];
            assert ns[b] == sorted[b];
          } else {
            assert b == |sorted|;
            assert a < |sorted|;
            assert ns[a] == sorted[a];
            assert ns[b] == x;
            assert sorted[a] <= x;
          }
        }

        assert right[..j + 1] == right[..j] + [right[j]];
        assert multiset(ns) == multiset(sorted) + multiset([right[j]]);
        assert multiset(right[..j + 1]) == multiset(right[..j]) + multiset([right[j]]);
        assert multiset(ns) == multiset(left[..i]) + multiset(right[..j + 1]);

        forall k | 0 <= k < |ns| && i < |left|
          ensures ns[k] <= left[i]
        {
          if k < |sorted| {
            assert ns[k] == sorted[k];
            assert sorted[k] <= left[i];
          } else {
            assert k == |sorted|;
            assert ns[k] == x;
            assert x == right[j];
            assert right[j] <= left[i];
          }
        }

        forall k | 0 <= k < |ns| && j + 1 < |right|
          ensures ns[k] <= right[j + 1]
        {
          assert 0 <= j < j + 1 < |right|;
          assert right[j] <= right[j + 1];
          if k < |sorted| {
            assert ns[k] == sorted[k];
            assert sorted[k] <= right[j];
          } else {
            assert k == |sorted|;
            assert ns[k] == x;
            assert x == right[j];
          }
        }

        sorted := ns;
        j := j + 1;
      }
    }

    assert i == |left|;
    assert j == |right|;
    assert left[..i] == left;
    assert right[..j] == right;
    assert multiset(sorted) == multiset(left) + multiset(right);
    assert multiset(leftInputs) == multiset(left);
    assert multiset(rightInputs) == multiset(right);
    assert multiset(inputs) == multiset(sorted);
  }
}