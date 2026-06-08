method p_6_2_c_replace_even_with_zero_array(inputs: array<int>) returns (result: array<int>)
	ensures result.Length == inputs.Length
	ensures forall i :: 0 <= i < inputs.Length ==> (inputs[i] % 2 == 0 ==> result[i] == 0) && (inputs[i] % 2 != 0 ==> result[i] == inputs[i])
{
  result := new int[inputs.Length];
  var i := 0;
  while i < inputs.Length
    invariant 0 <= i <= inputs.Length
    invariant result.Length == inputs.Length
    invariant forall j :: 0 <= j < i ==> (inputs[j] % 2 == 0 ==> result[j] == 0) && (inputs[j] % 2 != 0 ==> result[j] == inputs[j])
  {
    if inputs[i] % 2 == 0 {
      result[i] := 0;
    } else {
      result[i] := inputs[i];
    }
    i := i + 1;
  }
}