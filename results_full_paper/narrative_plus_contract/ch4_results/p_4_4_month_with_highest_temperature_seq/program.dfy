method p_4_4_month_with_highest_temperature_seq(inputs: seq<real>) returns (hottest: int)
	requires |inputs| == 12
	ensures 1 <= hottest <= 12
	ensures forall i :: 0 <= i <= |inputs| - 1 ==> inputs[hottest - 1] >= inputs[i]
{
  var maxIdx := 0;
  var i := 1;
  while i < |inputs|
    invariant 1 <= i <= |inputs|
    invariant 0 <= maxIdx < i
    invariant forall j :: 0 <= j < i ==> inputs[maxIdx] >= inputs[j]
    decreases |inputs| - i
  {
    if inputs[i] > inputs[maxIdx] {
      maxIdx := i;
    }
    i := i + 1;
  }
  hottest := maxIdx + 1;
}