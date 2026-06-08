method p_6_7_reverse_array_array(inputs: array<int>) returns (reversed: array<int>)
	ensures reversed.Length == inputs.Length
	ensures forall i :: 0 <= i < reversed.Length ==> reversed[i] == inputs[inputs.Length - 1 - i]
{
  reversed := new int[inputs.Length];
  var i := 0;
  while i < inputs.Length
    invariant 0 <= i <= inputs.Length
    invariant reversed.Length == inputs.Length
    invariant forall j :: 0 <= j < i ==> reversed[j] == inputs[inputs.Length - 1 - j]
  {
    reversed[i] := inputs[inputs.Length - 1 - i];
    i := i + 1;
  }
}