function contiguous_duplicates(inputs: seq<int>, i : int, j : int, d : int) : (b : bool) 
  requires 0 <= i < j < |inputs|
  decreases j - i
{
  if i + 1 == j then inputs[i] == inputs[j] == d
  else if inputs[i] == d then contiguous_duplicates(inputs, i + 1, j, d)
  else false
}

method p4_2_d_adjacent_duplicates(inputs: seq<int>) returns (duplicates: seq<int>)
	ensures forall d :: d in duplicates ==> d in inputs
	ensures forall i :: 0 <= i < |inputs| - 1 && inputs[i] == inputs[i + 1] ==> inputs[i] in duplicates
	ensures forall d :: d in duplicates ==> exists i :: 0 <= i < |inputs| - 1 && inputs[i] == inputs[i + 1] && inputs[i] == d
	ensures forall d :: d in duplicates ==> exists i, j :: 0 <= i < j < |inputs| && contiguous_duplicates(inputs, i, j, d) == true
{
  duplicates := [];

  var i := 0;
  while i < |inputs| - 1
    invariant 0 <= i <= |inputs|
    invariant forall d :: d in duplicates ==> d in inputs
    invariant forall d :: d in duplicates ==> exists k :: 0 <= k < i && inputs[k] == inputs[k+1] && inputs[k] == d
  {
    if inputs[i] == inputs[i+1] {
      var d := inputs[i];
      var found := false;
      var j := 0;
      while j < |duplicates|
        invariant 0 <= j <= |duplicates|
        invariant !found ==> forall k :: 0 <= k < j ==> duplicates[k] != d
      {
        if duplicates[j] == d {
          found := true;
        }
        j := j + 1;
      }
      if !found {
        duplicates := duplicates + [d];
      }
    }
    i := i + 1;
  }
}