method p_4_4_month_with_highest_temperature_array(inputs: array<real>) returns (hottest: int)
	requires inputs.Length == 12
	ensures 1 <= hottest <= 12
	ensures forall i :: 0 <= i <= inputs.Length - 1 ==> inputs[hottest - 1] >= inputs[i]
{
  hottest := 1;
  var idx := 1;

  forall i | 0 <= i < idx
    ensures inputs[hottest - 1] >= inputs[i]
  {
    assert i == 0;
    assert hottest - 1 == 0;
    assert inputs[hottest - 1] == inputs[i];
  }

  while idx < inputs.Length
    invariant 1 <= hottest <= inputs.Length
    invariant 1 <= idx <= inputs.Length
    invariant forall i :: 0 <= i < idx ==> inputs[hottest - 1] >= inputs[i]
    decreases inputs.Length - idx
  {
    if inputs[idx] > inputs[hottest - 1] {
      var previousHottest := hottest;
      assert inputs[idx] > inputs[previousHottest - 1];
      assert forall i :: 0 <= i < idx ==> inputs[previousHottest - 1] >= inputs[i];

      hottest := idx + 1;
      assert hottest - 1 == idx;
      assert inputs[hottest - 1] == inputs[idx];
      assert inputs[hottest - 1] >= inputs[idx];

      forall i | 0 <= i < idx
        ensures inputs[hottest - 1] >= inputs[i]
      {
        assert inputs[previousHottest - 1] >= inputs[i];
        assert inputs[idx] > inputs[previousHottest - 1];
        assert inputs[idx] >= inputs[i];
        assert inputs[hottest - 1] == inputs[idx];
      }
    } else {
      assert !(inputs[idx] > inputs[hottest - 1]);
      assert inputs[idx] <= inputs[hottest - 1];
      assert inputs[hottest - 1] >= inputs[idx];
    }

    assert inputs[hottest - 1] >= inputs[idx];
    assert forall i :: 0 <= i < idx ==> inputs[hottest - 1] >= inputs[i];

    forall i | 0 <= i < idx + 1
      ensures inputs[hottest - 1] >= inputs[i]
    {
      if i < idx {
        assert inputs[hottest - 1] >= inputs[i];
      } else {
        assert i == idx;
        assert inputs[hottest - 1] >= inputs[idx];
      }
    }

    idx := idx + 1;
  }

  assert idx == inputs.Length;
  assert inputs.Length == 12;
  assert 1 <= hottest <= 12;

  forall i | 0 <= i <= inputs.Length - 1
    ensures inputs[hottest - 1] >= inputs[i]
  {
    assert i < inputs.Length;
    assert i < idx;
    assert inputs[hottest - 1] >= inputs[i];
  }
}