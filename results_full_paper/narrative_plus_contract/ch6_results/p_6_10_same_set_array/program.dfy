function array_to_set(arr: seq<int>): set<int>
{
  if |arr| == 0 then {}
  else {arr[0]} + array_to_set(arr[1..])
}

method p_6_10_same_set_array(first: array<int>, second: array<int>) returns (are_same_set: bool)
	ensures are_same_set == (array_to_set(first[..]) == array_to_set(second[..]))
{
  var firstSet: set<int> := {};
  var i := first.Length;
  while i > 0
    invariant 0 <= i <= first.Length
    invariant firstSet == array_to_set(first[i..])
    decreases i
  {
    var k := i - 1;
    assert 0 <= k < first.Length;
    assert firstSet == array_to_set(first[k + 1..]);
    assert |first[k..]| > 0;
    assert first[k..][0] == first[k];
    assert first[k..][1..] == first[k + 1..];
    assert array_to_set(first[k..]) == {first[k]} + array_to_set(first[k + 1..]);
    firstSet := {first[k]} + firstSet;
    i := k;
    assert firstSet == array_to_set(first[i..]);
  }

  var secondSet: set<int> := {};
  var j := second.Length;
  while j > 0
    invariant 0 <= j <= second.Length
    invariant secondSet == array_to_set(second[j..])
    decreases j
  {
    var k := j - 1;
    assert 0 <= k < second.Length;
    assert secondSet == array_to_set(second[k + 1..]);
    assert |second[k..]| > 0;
    assert second[k..][0] == second[k];
    assert second[k..][1..] == second[k + 1..];
    assert array_to_set(second[k..]) == {second[k]} + array_to_set(second[k + 1..]);
    secondSet := {second[k]} + secondSet;
    j := k;
    assert secondSet == array_to_set(second[j..]);
  }

  assert first[0..] == first[..];
  assert second[0..] == second[..];
  assert firstSet == array_to_set(first[..]);
  assert secondSet == array_to_set(second[..]);
  are_same_set := firstSet == secondSet;
}