method p_6_2_h_is_sorted_seq(inputs: seq<int>) returns (is_sorted: bool)
	ensures is_sorted == (forall i :: 0 <= i < |inputs| - 1 ==> inputs[i] <= inputs[i + 1])
{
  is_sorted := forall i :: 0 <= i < |inputs| - 1 ==> inputs[i] <= inputs[i + 1];
}