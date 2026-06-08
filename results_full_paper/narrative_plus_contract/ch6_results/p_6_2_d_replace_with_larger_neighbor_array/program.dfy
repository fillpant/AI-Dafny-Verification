method p_6_2_d_replace_with_larger_neighbor_array(inputs: array<int>) returns (result: array<int>)
	requires inputs.Length >= 3
	ensures result.Length == inputs.Length
	ensures result[0] == inputs[0]
	ensures result[inputs.Length - 1] == inputs[inputs.Length - 1]
	ensures forall i :: 1 <= i < inputs.Length - 1 ==> result[i] == if inputs[i - 1] >= inputs[i + 1] then inputs[i - 1] else inputs[i + 1]
{
  result := new int[inputs.Length];
  var n := inputs.Length;

  result[0] := inputs[0];
  result[n - 1] := inputs[n - 1];

  var i := 1;
  while i < n - 1
    invariant n == inputs.Length
    invariant result.Length == n
    invariant 1 <= i <= n - 1
    invariant result[0] == inputs[0]
    invariant result[n - 1] == inputs[n - 1]
    invariant forall j :: 1 <= j < i ==> result[j] == if inputs[j - 1] >= inputs[j + 1] then inputs[j - 1] else inputs[j + 1]
  {
    result[i] := if inputs[i - 1] >= inputs[i + 1] then inputs[i - 1] else inputs[i + 1];
    i := i + 1;
  }
}