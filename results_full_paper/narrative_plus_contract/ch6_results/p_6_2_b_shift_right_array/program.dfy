method p_6_2_b_shift_right_array(inputs: array<int>) returns (result: array<int>)
	requires inputs.Length >= 1
	ensures result.Length == inputs.Length
	ensures result[0] == inputs[inputs.Length - 1]
	ensures forall i :: 1 <= i < inputs.Length ==> result[i] == inputs[i - 1]
{
  result := new int[inputs.Length];
  result[0] := inputs[inputs.Length - 1];

  var i := 1;
  while i < inputs.Length
    invariant 1 <= i <= inputs.Length
    invariant result.Length == inputs.Length
    invariant result[0] == inputs[inputs.Length - 1]
    invariant forall k :: 1 <= k < i ==> result[k] == inputs[k - 1]
    decreases inputs.Length - i
  {
    result[i] := inputs[i - 1];
    i := i + 1;
  }
}