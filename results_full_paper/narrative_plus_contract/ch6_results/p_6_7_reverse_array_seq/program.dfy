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
    var oldReversed := reversed;
    var oldI := i;

    forall j | 0 <= j < |oldReversed|
      ensures oldReversed[j] == inputs[|inputs| - 1 - j]
    {
      assert oldReversed == reversed;
      assert |oldReversed| == |reversed|;
      assert 0 <= j < |reversed|;
      assert oldReversed[j] == reversed[j];
      assert reversed[j] == inputs[|inputs| - 1 - j];
    }

    i := i - 1;
    assert oldI > 0;
    assert i == oldI - 1;
    assert 0 <= i < |inputs|;

    reversed := oldReversed + [inputs[i]];
    assert |oldReversed| == |inputs| - oldI;
    assert |reversed| == |oldReversed| + 1;
    assert |reversed| == |inputs| - i;

    forall j | 0 <= j < |reversed|
      ensures reversed[j] == inputs[|inputs| - 1 - j]
    {
      if j < |oldReversed| {
        assert 0 <= j < |oldReversed|;
        assert reversed[j] == (oldReversed + [inputs[i]])[j];
        assert (oldReversed + [inputs[i]])[j] == oldReversed[j];
        assert oldReversed[j] == inputs[|inputs| - 1 - j];
      } else {
        assert j >= |oldReversed|;
        assert j < |oldReversed| + 1;
        assert j == |oldReversed|;
        assert |[inputs[i]]| == 1;
        assert j - |oldReversed| == 0;
        assert 0 <= j - |oldReversed| < |[inputs[i]]|;
        assert reversed[j] == (oldReversed + [inputs[i]])[j];
        assert (oldReversed + [inputs[i]])[j] == [inputs[i]][j - |oldReversed|];
        assert [inputs[i]][0] == inputs[i];
        assert reversed[j] == inputs[i];
        assert |inputs| - 1 - j == i;
        assert reversed[j] == inputs[|inputs| - 1 - j];
      }
    }
  }

  assert i == 0;
  assert |reversed| == |inputs|;
  assert forall j :: 0 <= j < |reversed| ==> reversed[j] == inputs[|inputs| - 1 - j];
}