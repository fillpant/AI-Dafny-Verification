method p_4_4_month_with_highest_temperature_array(inputs: array<real>) returns (hottest: int)
	requires inputs.Length == 12
	ensures 1 <= hottest <= 12
	ensures forall i :: 0 <= i <= inputs.Length - 1 ==> inputs[hottest - 1] >= inputs[i]
{
  hottest := 1;
  var idx := 1;
  while idx < inputs.Length
    invariant 1 <= idx <= inputs.Length
    invariant 1 <= hottest <= idx
    invariant forall i :: 0 <= i < idx ==> inputs[hottest - 1] >= inputs[i]
    decreases inputs.Length - idx
  {
    if inputs[idx] > inputs[hottest - 1] {
      hottest := idx + 1;
    }
    idx := idx + 1;
  }
}