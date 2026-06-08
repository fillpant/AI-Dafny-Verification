method p_4_2_c_cumulative_totals_array(inputs: array<int>) returns (totals: array<int>)
	requires 0 < inputs.Length
	ensures totals.Length == inputs.Length
	ensures forall i :: 0 <= i < inputs.Length ==> totals[i] == (if i == 0 then inputs[0] else totals[i - 1] + inputs[i])
{
  totals := new int[inputs.Length];
  totals[0] := inputs[0];

  var i := 1;
  while i < inputs.Length
    invariant 1 <= i <= inputs.Length
    invariant totals.Length == inputs.Length
    invariant totals[0] == inputs[0]
    invariant forall j :: 1 <= j < i ==> totals[j] == totals[j - 1] + inputs[j]
  {
    totals[i] := totals[i - 1] + inputs[i];
    i := i + 1;
  }
}