method p4_2_c_cumulative_totals(inputs: seq<int>) returns (totals: seq<int>)
	requires 0 < |inputs|
	ensures |totals| == |inputs|
	ensures forall i :: 0 <= i < |inputs| ==> totals[i] == (if i == 0 then inputs[0] else totals[i - 1] + inputs[i])
{
  var res: seq<int> := [];
  var i: int := 0;
  while i < |inputs|
    invariant 0 <= i <= |inputs|
    invariant |res| == i
    invariant i == 0 ==> res == []
    invariant i > 0 ==> res[0] == inputs[0]
    invariant forall j :: 1 <= j < i ==> res[j] == res[j-1] + inputs[j]
  {
    if i == 0 {
      res := [inputs[0]];
    } else {
      res := res + [res[i-1] + inputs[i]];
    }
    i := i + 1;
  }
  totals := res;
}