method p_6_2_a_swap_first_last_seq(inputs: seq<int>) returns (result: seq<int>)
	requires |inputs| >= 2
	ensures |result| == |inputs|
	ensures result[0] == inputs[|inputs| - 1]
	ensures result[|inputs| - 1] == inputs[0]
	ensures forall i :: 1 <= i < |inputs| - 1 ==> result[i] == inputs[i]
{
  var n := |inputs|;

  assert 0 <= 0 < |inputs|;
  assert 0 <= n - 1 < |inputs|;
  var tmp := inputs[0 := inputs[n - 1]];
  assert |tmp| == n;

  assert 0 <= n - 1 < |tmp|;
  result := tmp[n - 1 := inputs[0]];
  assert |result| == n;

  assert 1 <= n - 1;
  assert n - 1 != 0;
  assert 0 <= 0 < |result|;
  assert 0 <= 0 < |tmp|;
  assert result[0] == tmp[0];
  assert tmp[0] == inputs[n - 1];
  assert result[0] == inputs[n - 1];

  assert 0 <= n - 1 < |result|;
  assert result[n - 1] == inputs[0];

  forall i | 1 <= i < n - 1
    ensures result[i] == inputs[i]
  {
    assert 0 <= i;
    assert i < n;
    assert i < |result|;
    assert i < |tmp|;
    assert i < |inputs|;
    assert i != n - 1;
    assert i != 0;
    assert result[i] == tmp[i];
    assert tmp[i] == inputs[i];
  }
}