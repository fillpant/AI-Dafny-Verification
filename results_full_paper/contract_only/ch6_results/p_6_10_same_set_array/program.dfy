function array_to_set(arr: seq<int>): set<int>
{
  if |arr| == 0 then {}
  else {arr[0]} + array_to_set(arr[1..])
}

method p_6_10_same_set_array(first: array<int>, second: array<int>) returns (are_same_set: bool)
	ensures are_same_set == (array_to_set(first[..]) == array_to_set(second[..]))
{
  are_same_set := array_to_set(first[..]) == array_to_set(second[..]);
}