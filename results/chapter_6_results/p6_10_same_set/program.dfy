function array_to_set(arr: seq<int>) : set<int>
{
  if |arr| == 0 then {}
  else {arr[0]} + array_to_set(arr[1..])
}

method p6_10_same_set(arr1: seq<int>, arr2: seq<int>) returns (areSameSet: bool)
	ensures areSameSet == (array_to_set(arr1) == array_to_set(arr2))
{
  var s1: set<int> := {};
  var i := |arr1|;
  while i > 0
    invariant 0 <= i <= |arr1|
    invariant s1 == array_to_set(arr1[i..])
  {
    s1 := s1 + {arr1[i-1]};
    i := i - 1;
  }

  var s2: set<int> := {};
  var j := |arr2|;
  while j > 0
    invariant 0 <= j <= |arr2|
    invariant s2 == array_to_set(arr2[j..])
  {
    s2 := s2 + {arr2[j-1]};
    j := j - 1;
  }

  areSameSet := (s1 == s2);
}