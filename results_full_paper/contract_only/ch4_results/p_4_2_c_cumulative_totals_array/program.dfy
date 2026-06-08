method p_4_2_c_cumulative_totals_array(inputs: array<int>) returns (totals: array<int>)
	requires 0 < inputs.Length
	ensures totals.Length == inputs.Length
	ensures forall i :: 0 <= i < inputs.Length ==> totals[i] == (if i == 0 then inputs[0] else totals[i - 1] + inputs[i])
{
  totals := new int[inputs.Length];
  totals[0] := inputs[0];

  var i := 1;
  while i < inputs.Length
    invariant 1 <= i <= inputs.Length
    invariant totals.Length == inputs.Length
    invariant totals[0] == inputs[0]
    invariant forall j :: 1 <= j < i ==> totals[j] == totals[j - 1] + inputs[j]
  {
    var n := i;
    totals[n] := totals[n - 1] + inputs[n];

    assert n != 0;
    assert totals[0] == inputs[0];

    assert forall j :: 1 <= j < n + 1 ==> totals[j] == totals[j - 1] + inputs[j] by {
      forall j | 1 <= j < n + 1
        ensures totals[j] == totals[j - 1] + inputs[j]
      {
        if j == n {
          assert totals[j] == totals[j - 1] + inputs[j];
        } else {
          assert j < n;
          assert 1 <= j < i;
          assert totals[j] == totals[j - 1] + inputs[j];
        }
      }
    }

    i := n + 1;
  }

  assert i == inputs.Length;
  assert forall k :: 0 <= k < inputs.Length ==> totals[k] == (if k == 0 then inputs[0] else totals[k - 1] + inputs[k]) by {
    forall k | 0 <= k < inputs.Length
      ensures totals[k] == (if k == 0 then inputs[0] else totals[k - 1] + inputs[k])
    {
      if k == 0 {
        assert totals[k] == inputs[0];
      } else {
        assert 1 <= k < i;
        assert totals[k] == totals[k - 1] + inputs[k];
      }
    }
  }
}