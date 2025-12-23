method p4_5_month_with_highest_temperature(inputs: seq<real>) returns (hottest: int)
	requires |inputs| == 12
	ensures 1 <= hottest <= 12
	ensures forall i :: 0 <= i <= |inputs|-1 ==> inputs[hottest-1] >= inputs[i]
{
  var maxIndex := 0;
  var maxVal := inputs[0];
  var i := 1;
  while i < 12
    invariant 1 <= i <= 12
    invariant 0 <= maxIndex < i
    invariant maxVal == inputs[maxIndex]
    invariant forall j :: 0 <= j < i ==> maxVal >= inputs[j]
  {
    if inputs[i] > maxVal {
      maxVal := inputs[i];
      maxIndex := i;
    }
    i := i + 1;
  }
  hottest := maxIndex + 1;
}