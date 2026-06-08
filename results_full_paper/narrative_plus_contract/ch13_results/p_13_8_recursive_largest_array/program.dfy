function find_largest(inputs: seq<int>): int
  requires |inputs| >= 1
  ensures forall x :: x in inputs ==> find_largest(inputs) >= x
{
  if |inputs| == 1 then inputs[0]
  else 
      assert inputs == [inputs[0]] + inputs[1..];
      var sub_largest := find_largest(inputs[1..]) ;
      if inputs[0] >= sub_largest then inputs[0] else sub_largest
}

method p_13_8_recursive_largest_array(inputs: array<int>) returns (largest: int)
	requires inputs.Length >= 1
	ensures largest == find_largest(inputs[..])
{
  var n := inputs.Length;
  var i := n - 1;
  largest := inputs[i];

  assert |inputs[i..]| == 1;
  assert inputs[i..][0] == inputs[i];
  assert find_largest(inputs[i..]) == inputs[i];

  while i > 0
    invariant n == inputs.Length
    invariant 0 <= i < n
    invariant largest == find_largest(inputs[i..])
  {
    var j := i - 1;
    assert 0 <= j < n;
    assert i == j + 1;
    assert |inputs[j..]| > 1;
    assert inputs[j..][0] == inputs[j];

    assert inputs[j..][1..] == inputs[i..] by {
      assert |inputs[j..][1..]| == |inputs[i..]|;
      forall k | 0 <= k < |inputs[i..]|
        ensures inputs[j..][1..][k] == inputs[i..][k]
      {
        assert inputs[j..][1..][k] == inputs[j..][k + 1];
        assert inputs[j..][k + 1] == inputs[j + k + 1];
        assert inputs[i..][k] == inputs[i + k];
        assert j + k + 1 == i + k;
      }
    }
    assert find_largest(inputs[j..][1..]) == largest;

    if inputs[j] >= largest {
      assert find_largest(inputs[j..]) == inputs[j];
      largest := inputs[j];
    } else {
      assert find_largest(inputs[j..]) == largest;
    }

    i := j;
  }

  assert i == 0;
  assert inputs[i..] == inputs[..];
}