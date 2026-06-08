method p_6_2_a_swap_first_last_array(inputs: array<int>) returns (result: array<int>)
	requires inputs.Length >= 2
	ensures result.Length == inputs.Length
	ensures result[0] == inputs[inputs.Length - 1]
	ensures result[inputs.Length - 1] == inputs[0]
	ensures forall i :: 1 <= i < inputs.Length - 1 ==> result[i] == inputs[i]
{
  result := new int[inputs.Length];
  var n := inputs.Length;
  result[0] := inputs[n - 1];
  result[n - 1] := inputs[0];

  var i := 1;
  while i < n - 1
    invariant 1 <= i <= n - 1
    invariant result.Length == n
    invariant result[0] == inputs[n - 1]
    invariant result[n - 1] == inputs[0]
    invariant forall j :: 1 <= j < i ==> result[j] == inputs[j]
  {
    result[i] := inputs[i];
    i := i + 1;
  }
}