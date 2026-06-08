method p_4_4_month_with_highest_temperature_seq(inputs: seq<real>) returns (hottest: int)
	requires |inputs| == 12
	ensures 1 <= hottest <= 12
	ensures forall i :: 0 <= i <= |inputs| - 1 ==> inputs[hottest - 1] >= inputs[i]
{
  var maxIdx: int := 0;
  var i: int := 1;

  while i < |inputs|
    invariant |inputs| == 12
    invariant 1 <= i <= |inputs|
    invariant 0 <= maxIdx < i
    invariant forall j :: 0 <= j < i ==> inputs[maxIdx] >= inputs[j]
    decreases |inputs| - i
  {
    if inputs[i] > inputs[maxIdx] {
      var prev := maxIdx;
      assert inputs[i] > inputs[prev];
      assert forall j :: 0 <= j < i ==> inputs[prev] >= inputs[j];

      maxIdx := i;
      assert inputs[maxIdx] >= inputs[i];

      assert forall j :: 0 <= j < i ==> inputs[maxIdx] >= inputs[j] by {
        forall j | 0 <= j < i
          ensures inputs[maxIdx] >= inputs[j]
        {
          assert inputs[prev] >= inputs[j];
          assert inputs[maxIdx] == inputs[i];
          assert inputs[i] > inputs[prev];
        }
      }
    } else {
      assert inputs[maxIdx] >= inputs[i];
      assert forall j :: 0 <= j < i ==> inputs[maxIdx] >= inputs[j];
    }

    assert forall j :: 0 <= j < i ==> inputs[maxIdx] >= inputs[j];
    assert forall j :: 0 <= j < i + 1 ==> inputs[maxIdx] >= inputs[j] by {
      forall j | 0 <= j < i + 1
        ensures inputs[maxIdx] >= inputs[j]
      {
        if j < i {
          assert inputs[maxIdx] >= inputs[j];
        } else {
          assert j == i;
          assert inputs[maxIdx] >= inputs[i];
        }
      }
    }

    i := i + 1;
  }

  hottest := maxIdx + 1;
  assert i == |inputs|;
  assert 0 <= maxIdx < |inputs|;
  assert |inputs| == 12;
  assert maxIdx < 12;
  assert maxIdx <= 11;
  assert 1 <= hottest <= 12;
  assert hottest - 1 == maxIdx;

  assert forall j :: 0 <= j <= |inputs| - 1 ==> inputs[hottest - 1] >= inputs[j] by {
    forall j | 0 <= j <= |inputs| - 1
      ensures inputs[hottest - 1] >= inputs[j]
    {
      assert j < |inputs|;
      assert inputs[maxIdx] >= inputs[j];
      assert hottest - 1 == maxIdx;
    }
  }
}