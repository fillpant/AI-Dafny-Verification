method p_6_2_j_has_duplicates_seq(inputs: seq<int>) returns (has_duplicates: bool)
	requires |inputs| >= 2
	ensures has_duplicates == (exists i, j :: 0 <= i < j < |inputs| && inputs[i] == inputs[j])
{
  if exists i, j :: 0 <= i < j < |inputs| && inputs[i] == inputs[j] {
    has_duplicates := true;
  } else {
    has_duplicates := false;
  }
}