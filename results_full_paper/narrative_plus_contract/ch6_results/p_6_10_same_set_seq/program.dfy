function array_to_set(arr: seq<int>): set<int>
{
  if |arr| == 0 then {}
  else {arr[0]} + array_to_set(arr[1..])
}

method p_6_10_same_set_seq(first: seq<int>, second: seq<int>) returns (are_same_set: bool)
	ensures are_same_set == (array_to_set(first) == array_to_set(second))
{
  var fSub := forall i: int | 0 <= i < |first| :: first[i] in second;
  var sSub := forall j: int | 0 <= j < |second| :: second[j] in first;
  are_same_set := fSub && sSub;

  ghost var sf: set<int> := {};
  var i := |first|;
  while 0 < i
    invariant 0 <= i <= |first|
    invariant sf == array_to_set(first[i..])
    invariant forall x: int :: x in sf <==> x in first[i..]
  {
    ghost var oldSf := sf;
    ghost var oldI := i;
    i := i - 1;
    assert oldI == i + 1;
    assert oldSf == array_to_set(first[i+1..]);
    assert first[i..] == [first[i]] + first[i+1..];
    assert |first[i..]| > 0;
    assert first[i..][0] == first[i];
    assert first[i..][1..] == first[i+1..];
    sf := {first[i]} + oldSf;
    assert array_to_set(first[i..]) == {first[i]} + array_to_set(first[i+1..]);
    assert sf == array_to_set(first[i..]);
    assert forall x: int :: x in sf <==> x in first[i..];
  }
  assert first[0..] == first;
  assert sf == array_to_set(first);
  assert forall x: int :: x in sf <==> x in first;

  ghost var ss: set<int> := {};
  var j := |second|;
  while 0 < j
    invariant 0 <= j <= |second|
    invariant ss == array_to_set(second[j..])
    invariant forall x: int :: x in ss <==> x in second[j..]
  {
    ghost var oldSs := ss;
    ghost var oldJ := j;
    j := j - 1;
    assert oldJ == j + 1;
    assert oldSs == array_to_set(second[j+1..]);
    assert second[j..] == [second[j]] + second[j+1..];
    assert |second[j..]| > 0;
    assert second[j..][0] == second[j];
    assert second[j..][1..] == second[j+1..];
    ss := {second[j]} + oldSs;
    assert array_to_set(second[j..]) == {second[j]} + array_to_set(second[j+1..]);
    assert ss == array_to_set(second[j..]);
    assert forall x: int :: x in ss <==> x in second[j..];
  }
  assert second[0..] == second;
  assert ss == array_to_set(second);
  assert forall x: int :: x in ss <==> x in second;

  if fSub && sSub {
    forall x: int | x in sf
      ensures x in ss
    {
      assert x in first;
      var k :| 0 <= k < |first| && first[k] == x;
      assert first[k] in second;
      assert x in second;
      assert x in ss;
    }
    forall x: int | x in ss
      ensures x in sf
    {
      assert x in second;
      var k :| 0 <= k < |second| && second[k] == x;
      assert second[k] in first;
      assert x in first;
      assert x in sf;
    }
    assert sf <= ss;
    assert ss <= sf;
    assert sf == ss;
  } else {
    if !fSub {
      var k :| 0 <= k < |first| && !(first[k] in second);
      assert first[k] in first;
      assert first[k] in sf;
      assert !(first[k] in ss);
      assert sf != ss;
    } else {
      assert !sSub;
      var k :| 0 <= k < |second| && !(second[k] in first);
      assert second[k] in second;
      assert second[k] in ss;
      assert !(second[k] in sf);
      assert sf != ss;
    }
  }

  assert are_same_set == (sf == ss);
  assert are_same_set == (array_to_set(first) == array_to_set(second));
}