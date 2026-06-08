method p_4_2_c_cumulative_totals_seq(inputs: seq<int>) returns (totals: seq<int>)
	requires 0 < |inputs|
	ensures |totals| == |inputs|
	ensures forall i :: 0 <= i < |inputs| ==> totals[i] == (if i == 0 then inputs[0] else totals[i - 1] + inputs[i])
{
  totals := [inputs[0]];
  var n := |inputs|;
  var k := 1;

  while k < n
    invariant n == |inputs|
    invariant 1 <= k <= n
    invariant |totals| == k
    invariant forall j :: 0 <= j < k ==> totals[j] == (if j == 0 then inputs[0] else totals[j - 1] + inputs[j])
    decreases n - k
  {
    var prevTotals := totals;
    assert |prevTotals| == k;
    assert forall j :: 0 <= j < k ==> prevTotals[j] == (if j == 0 then inputs[0] else prevTotals[j - 1] + inputs[j]);

    var next := prevTotals[k - 1] + inputs[k];
    totals := prevTotals + [next];

    forall j | 0 <= j < k
      ensures totals[j] == prevTotals[j]
    {
      assert 0 <= j < |prevTotals|;
      assert totals == prevTotals + [next];
      assert totals[j] == (prevTotals + [next])[j];
      assert (prevTotals + [next])[j] == prevTotals[j];
    }

    forall j | 0 <= j < k + 1
      ensures totals[j] == (if j == 0 then inputs[0] else totals[j - 1] + inputs[j])
    {
      if j < k {
        assert 0 <= j < k;
        assert totals[j] == prevTotals[j];
        assert prevTotals[j] == (if j == 0 then inputs[0] else prevTotals[j - 1] + inputs[j]);
        if j == 0 {
          assert prevTotals[j] == inputs[0];
        } else {
          assert 0 <= j - 1 < k;
          assert totals[j - 1] == prevTotals[j - 1];
          assert prevTotals[j] == prevTotals[j - 1] + inputs[j];
        }
      } else {
        assert j == k;
        assert 0 < j;
        assert j - 1 == k - 1;
        assert totals[j] == next;
        assert totals[j - 1] == prevTotals[k - 1];
        assert next == prevTotals[k - 1] + inputs[k];
      }
    }

    k := k + 1;
  }
}