function array_to_set(arr: seq<int>): set<int>
{
  if |arr| == 0 then {}
  else {arr[0]} + array_to_set(arr[1..])
}

method p_6_10_same_set_seq(first: seq<int>, second: seq<int>) returns (are_same_set: bool)
	ensures are_same_set == (array_to_set(first) == array_to_set(second))
{
  var i := |first|;
  assert first[i..] == [];
  assert array_to_set(first[i..]) == {};
  assert forall x :: x in array_to_set(first[i..]) <==> x in first[i..];
  while i > 0
    invariant 0 <= i <= |first|
    invariant forall x :: x in array_to_set(first[i..]) <==> x in first[i..]
    decreases i
  {
    var j := i;
    i := i - 1;
    assert 0 <= i < |first|;
    assert j == i + 1;
    assert |first[i..]| > 0;
    assert first[i..][0] == first[i];
    assert first[i..][1..] == first[j..];
    assert first[i..] == [first[i]] + first[j..];
    assert array_to_set(first[i..]) == {first[i]} + array_to_set(first[j..]);
    assert forall x :: x in array_to_set(first[i..]) <==> x in first[i..] by {
      forall x
        ensures x in array_to_set(first[i..]) <==> x in first[i..]
      {
        assert x in array_to_set(first[j..]) <==> x in first[j..];
        assert x in array_to_set(first[i..]) <==> x in {first[i]} + array_to_set(first[j..]);
        assert x in {first[i]} + array_to_set(first[j..]) <==> x == first[i] || x in array_to_set(first[j..]);
        assert x in first[i..] <==> x in [first[i]] + first[j..];
        assert x in [first[i]] + first[j..] <==> x == first[i] || x in first[j..];
      }
    }
  }
  assert i == 0;
  assert first[i..] == first;
  assert forall x :: x in array_to_set(first) <==> x in first;

  var k := |second|;
  assert second[k..] == [];
  assert array_to_set(second[k..]) == {};
  assert forall x :: x in array_to_set(second[k..]) <==> x in second[k..];
  while k > 0
    invariant 0 <= k <= |second|
    invariant forall x :: x in array_to_set(second[k..]) <==> x in second[k..]
    decreases k
  {
    var j := k;
    k := k - 1;
    assert 0 <= k < |second|;
    assert j == k + 1;
    assert |second[k..]| > 0;
    assert second[k..][0] == second[k];
    assert second[k..][1..] == second[j..];
    assert second[k..] == [second[k]] + second[j..];
    assert array_to_set(second[k..]) == {second[k]} + array_to_set(second[j..]);
    assert forall x :: x in array_to_set(second[k..]) <==> x in second[k..] by {
      forall x
        ensures x in array_to_set(second[k..]) <==> x in second[k..]
      {
        assert x in array_to_set(second[j..]) <==> x in second[j..];
        assert x in array_to_set(second[k..]) <==> x in {second[k]} + array_to_set(second[j..]);
        assert x in {second[k]} + array_to_set(second[j..]) <==> x == second[k] || x in array_to_set(second[j..]);
        assert x in second[k..] <==> x in [second[k]] + second[j..];
        assert x in [second[k]] + second[j..] <==> x == second[k] || x in second[j..];
      }
    }
  }
  assert k == 0;
  assert second[k..] == second;
  assert forall x :: x in array_to_set(second) <==> x in second;

  are_same_set := (forall x | x in first :: x in second) &&
                  (forall x | x in second :: x in first);

  assert are_same_set ==> (forall x :: x in first <==> x in second) by {
    if are_same_set {
      assert forall x :: x in first <==> x in second by {
        forall x
          ensures x in first <==> x in second
        {
          if x in first {
            assert x in second;
          }
          if x in second {
            assert x in first;
          }
        }
      }
    }
  }
  assert (forall x :: x in first <==> x in second) ==> are_same_set by {
    if (forall x :: x in first <==> x in second) {
      assert (forall x | x in first :: x in second) by {
        forall x | x in first
          ensures x in second
        {
          assert x in first <==> x in second;
        }
      }
      assert (forall x | x in second :: x in first) by {
        forall x | x in second
          ensures x in first
        {
          assert x in first <==> x in second;
        }
      }
    }
  }
  assert are_same_set == (forall x :: x in first <==> x in second);

  assert (forall x :: x in first <==> x in second) ==> array_to_set(first) == array_to_set(second) by {
    if (forall x :: x in first <==> x in second) {
      assert forall x :: x in array_to_set(first) <==> x in array_to_set(second) by {
        forall x
          ensures x in array_to_set(first) <==> x in array_to_set(second)
        {
          assert x in array_to_set(first) <==> x in first;
          assert x in array_to_set(second) <==> x in second;
          assert x in first <==> x in second;
        }
      }
      assert array_to_set(first) == array_to_set(second);
    }
  }
  assert array_to_set(first) == array_to_set(second) ==> (forall x :: x in first <==> x in second) by {
    if array_to_set(first) == array_to_set(second) {
      assert forall x :: x in first <==> x in second by {
        forall x
          ensures x in first <==> x in second
        {
          assert x in array_to_set(first) <==> x in first;
          assert x in array_to_set(second) <==> x in second;
          assert x in array_to_set(first) <==> x in array_to_set(second);
        }
      }
    }
  }
  assert (array_to_set(first) == array_to_set(second)) == (forall x :: x in first <==> x in second);
}