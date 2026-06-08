method p_6_2_i_has_adjacent_duplicates_seq(inputs: seq<int>) returns (has_duplicates: bool)
	requires |inputs| >= 2
	ensures has_duplicates == (exists i :: 0 <= i < |inputs| - 1 && inputs[i] == inputs[i + 1])
{
  var i := 0;
  while i < |inputs| - 1
    invariant 0 <= i <= |inputs| - 1
    invariant forall j :: 0 <= j < i ==> inputs[j] != inputs[j + 1]
  {
    if inputs[i] == inputs[i + 1] {
      has_duplicates := true;
      assert exists j :: 0 <= j < |inputs| - 1 && inputs[j] == inputs[j + 1];
      return;
    }
    i := i + 1;
  }
  has_duplicates := false;
}