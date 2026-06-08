function find_largest(inputs: seq<int>): (ret: int)
  requires |inputs| >= 1
  ensures forall x :: x in inputs ==> x <= ret
{
  if |inputs| == 1 then inputs[0]
  else 
    assert 2 <= |inputs|;
    var rest_largest := find_largest(inputs[1..]);
    var ret: int := if inputs[0] >= rest_largest then inputs[0] else rest_largest;
    assert inputs == [inputs[0]] + inputs[1..]; 
    ret 
} 

method p_6_2_g_second_largest_array(inputs: array<int>) returns (second_largest: int)
	requires inputs.Length >= 2
	ensures second_largest <= find_largest(inputs[..])
	ensures forall x :: x in inputs[..] ==> x < find_largest(inputs[..]) ==> x <= second_largest
{
  var i := 1;
  var maxIndex := 0;
  second_largest := inputs[0];

  while i < inputs.Length
    invariant 1 <= i <= inputs.Length
    invariant 0 <= maxIndex < i
    invariant second_largest == inputs[maxIndex]
    invariant forall k :: 0 <= k < i ==> inputs[k] <= second_largest
    decreases inputs.Length - i
  {
    var oldI := i;

    if inputs[oldI] > second_largest {
      second_largest := inputs[oldI];
      maxIndex := oldI;
    }

    assert forall k :: 0 <= k < oldI ==> inputs[k] <= second_largest;
    assert inputs[oldI] <= second_largest;

    i := oldI + 1;

    assert 1 <= i <= inputs.Length;
    assert 0 <= maxIndex < i;
    assert second_largest == inputs[maxIndex];

    forall k | 0 <= k < i
      ensures inputs[k] <= second_largest
    {
      if k == oldI {
        assert inputs[k] <= second_largest;
      } else {
        assert k < oldI;
        assert inputs[k] <= second_largest;
      }
    }
  }

  assert i == inputs.Length;
  assert forall k :: 0 <= k < inputs.Length ==> inputs[k] <= second_largest;

  assert 0 <= maxIndex < inputs.Length;
  assert |inputs[..]| == inputs.Length;
  assert 0 <= maxIndex < |inputs[..]|;
  assert inputs[..][maxIndex] == inputs[maxIndex];
  assert second_largest == inputs[..][maxIndex];
  assert second_largest in inputs[..];

  forall x | x in inputs[..]
    ensures x <= second_largest
  {
    assert exists k :: 0 <= k < |inputs[..]| && inputs[..][k] == x;
    var k :| 0 <= k < |inputs[..]| && inputs[..][k] == x;
    assert |inputs[..]| == inputs.Length;
    assert 0 <= k < inputs.Length;
    assert inputs[..][k] == inputs[k];
    assert inputs[k] == x;
    assert inputs[k] <= second_largest;
  }
}