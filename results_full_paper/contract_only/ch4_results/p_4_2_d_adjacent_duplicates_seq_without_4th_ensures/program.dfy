method p_4_2_d_adjacent_duplicates_seq_without_4th_ensures(inputs: seq<int>) returns (duplicates: seq<int>)
	ensures forall d :: d in duplicates ==> d in inputs
	ensures forall i :: 0 <= i < |inputs| - 1 && inputs[i] == inputs[i + 1] ==> inputs[i] in duplicates
	ensures forall d :: d in duplicates ==> exists i :: 0 <= i < |inputs| - 1 && inputs[i] == inputs[i + 1] && inputs[i] == d
{
  duplicates := [];
  var i := 0;

  while i < |inputs| - 1
    invariant 0 <= i <= |inputs|
    invariant forall d :: d in duplicates ==> d in inputs
    invariant forall d :: d in duplicates ==> exists j :: 0 <= j < i && j < |inputs| - 1 && inputs[j] == inputs[j + 1] && inputs[j] == d
    invariant forall j :: 0 <= j < i && j < |inputs| - 1 && inputs[j] == inputs[j + 1] ==> inputs[j] in duplicates
    decreases |inputs| - i
  {
    if inputs[i] == inputs[i + 1] {
      duplicates := duplicates + [inputs[i]];
    }
    i := i + 1;
  }
}