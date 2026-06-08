method p_6_2_j_has_duplicates_array(inputs: array<int>) returns (has_duplicates: bool)
	requires inputs.Length >= 2
	ensures has_duplicates == (exists i, j :: 0 <= i < j < inputs.Length && inputs[i] == inputs[j])
{
  has_duplicates := exists i, j :: 0 <= i < j < inputs.Length && inputs[i] == inputs[j];
}