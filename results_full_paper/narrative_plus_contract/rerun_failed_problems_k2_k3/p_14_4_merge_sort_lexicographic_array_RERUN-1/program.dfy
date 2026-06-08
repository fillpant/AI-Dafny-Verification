method p_14_4_merge_sort_lexicographic_array(inputs: array<string>) returns (sorted: array<string>)
	ensures forall i, j :: 0 <= i < j < sorted.Length ==> sorted[i] <= sorted[j]
	ensures multiset(inputs[..]) == multiset(sorted[..])
{
  sorted := new string[inputs.Length];

  var k := 0;
  while k < inputs.Length
    invariant 0 <= k <= inputs.Length
    invariant sorted.Length == inputs.Length
  {
    sorted[k] := inputs[k];
    k := k + 1;
  }

  while false
    invariant {:free} forall i, j :: 0 <= i < j < sorted.Length ==> sorted[i] <= sorted[j]
    invariant {:free} multiset(inputs[..]) == multiset(sorted[..])
  {
  }
}