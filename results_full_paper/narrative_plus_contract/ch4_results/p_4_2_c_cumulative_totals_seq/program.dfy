method p_4_2_c_cumulative_totals_seq(inputs: seq<int>) returns (totals: seq<int>)
	requires 0 < |inputs|
	ensures |totals| == |inputs|
	ensures forall i :: 0 <= i < |inputs| ==> totals[i] == (if i == 0 then inputs[0] else totals[i - 1] + inputs[i])
{
  totals := [inputs[0]];
  assert |totals| == 1;
  assert totals[0] == inputs[0];
  assert forall j :: 0 <= j < 1 ==> totals[j] == (if j == 0 then inputs[0] else totals[j - 1] + inputs[j]) by {
    forall j | 0 <= j < 1
      ensures totals[j] == (if j == 0 then inputs[0] else totals[j - 1] + inputs[j])
    {
      assert j == 0;
      assert totals[j] == inputs[0];
    }
  }

  var i := 1;
  while i < |inputs|
    invariant 1 <= i <= |inputs|
    invariant |totals| == i
    invariant forall j :: 0 <= j < i ==> totals[j] == (if j == 0 then inputs[0] else totals[j - 1] + inputs[j])
  {
    var oldTotals := totals;
    assert |oldTotals| == i;

    totals := oldTotals + [oldTotals[i - 1] + inputs[i]];
    assert |totals| == i + 1;

    assert forall j :: 0 <= j < i + 1 ==> totals[j] == (if j == 0 then inputs[0] else totals[j - 1] + inputs[j]) by {
      forall j | 0 <= j < i + 1
        ensures totals[j] == (if j == 0 then inputs[0] else totals[j - 1] + inputs[j])
      {
        if j < i {
          assert 0 <= j < |oldTotals|;
          assert totals[j] == oldTotals[j];
          assert oldTotals[j] == (if j == 0 then inputs[0] else oldTotals[j - 1] + inputs[j]);
          if j == 0 {
            assert totals[j] == inputs[0];
          } else {
            assert 0 <= j - 1 < |oldTotals|;
            assert totals[j - 1] == oldTotals[j - 1];
            assert totals[j] == totals[j - 1] + inputs[j];
          }
        } else {
          assert j == i;
          assert j != 0;
          assert totals[j] == oldTotals[i - 1] + inputs[i];
          assert 0 <= i - 1 < |oldTotals|;
          assert totals[i - 1] == oldTotals[i - 1];
          assert j - 1 == i - 1;
          assert totals[j - 1] == oldTotals[i - 1];
          assert inputs[j] == inputs[i];
          assert totals[j] == totals[j - 1] + inputs[j];
        }
      }
    }

    i := i + 1;
  }

  assert i == |inputs|;
  assert |totals| == |inputs|;
  assert forall j :: 0 <= j < |inputs| ==> totals[j] == (if j == 0 then inputs[0] else totals[j - 1] + inputs[j]) by {
    forall j | 0 <= j < |inputs|
      ensures totals[j] == (if j == 0 then inputs[0] else totals[j - 1] + inputs[j])
    {
      assert j < i;
    }
  }
}