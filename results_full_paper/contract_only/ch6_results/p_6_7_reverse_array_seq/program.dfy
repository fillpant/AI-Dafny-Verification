method p_6_7_reverse_array_seq(inputs: seq<int>) returns (reversed: seq<int>)
	ensures |reversed| == |inputs|
	ensures forall i :: 0 <= i < |reversed| ==> reversed[i] == inputs[|inputs| - 1 - i]
{
  reversed := [];
  var i := |inputs|;
  while i > 0
    invariant 0 <= i <= |inputs|
    invariant |reversed| == |inputs| - i
    invariant forall j :: 0 <= j < |reversed| ==> reversed[j] == inputs[|inputs| - 1 - j]
    decreases i
  {
    var prev := reversed;
    var oldI := i;
    i := i - 1;
    reversed := prev + [inputs[i]];

    assert oldI == i + 1;
    assert |prev| == |inputs| - oldI;
    assert |prev| == |inputs| - (i + 1);
    assert |prev| == |inputs| - 1 - i;

    assert forall j :: 0 <= j < |reversed| ==> reversed[j] == inputs[|inputs| - 1 - j] by {
      forall j | 0 <= j < |reversed|
        ensures reversed[j] == inputs[|inputs| - 1 - j]
      {
        if j < |prev| {
          assert reversed[j] == prev[j];
          assert prev[j] == inputs[|inputs| - 1 - j];
        } else {
          assert j == |prev|;
          assert |inputs| - 1 - j == i;
          assert reversed[j] == inputs[i];
        }
      }
    }
  }
}