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
  var largest := inputs[0];
  var i := 1;

  assert 0 <= 0 < 1 && inputs[0] == largest;
  assert exists k :: 0 <= k < 1 && inputs[k] == largest;
  forall k | 0 <= k < 1
    ensures inputs[k] <= largest
  {
    assert k == 0;
  }

  while i < inputs.Length
    invariant 1 <= i <= inputs.Length
    invariant forall k :: 0 <= k < i ==> inputs[k] <= largest
    invariant exists k :: 0 <= k < i && inputs[k] == largest
  {
    if inputs[i] > largest {
      var oldLargest := largest;
      largest := inputs[i];
      assert oldLargest < largest;
      forall k | 0 <= k < i
        ensures inputs[k] <= largest
      {
        assert inputs[k] <= oldLargest;
        assert oldLargest < largest;
      }
      assert inputs[i] == largest;
      assert 0 <= i < i + 1;
      assert exists k :: 0 <= k < i + 1 && inputs[k] == largest;
    } else {
      assert inputs[i] <= largest;
      var w :| 0 <= w < i && inputs[w] == largest;
      assert 0 <= w < i + 1 && inputs[w] == largest;
      assert exists k :: 0 <= k < i + 1 && inputs[k] == largest;
    }

    forall k | 0 <= k < i + 1
      ensures inputs[k] <= largest
    {
      if k < i {
        assert inputs[k] <= largest;
      } else {
        assert k == i;
        assert inputs[k] <= largest;
      }
    }

    i := i + 1;
  }

  second_largest := largest;

  assert i == inputs.Length;
  var w :| 0 <= w < inputs.Length && inputs[w] == second_largest;
  assert |inputs[..]| == inputs.Length;
  assert inputs[..][w] == inputs[w];
  assert exists k :: 0 <= k < |inputs[..]| && inputs[..][k] == second_largest;
  assert second_largest in inputs[..];

  forall x | x in inputs[..]
    ensures x <= second_largest
  {
    assert exists k :: 0 <= k < |inputs[..]| && inputs[..][k] == x;
    var k :| 0 <= k < |inputs[..]| && inputs[..][k] == x;
    assert |inputs[..]| == inputs.Length;
    assert inputs[..][k] == inputs[k];
    assert x == inputs[k];
    assert inputs[k] <= largest;
  }
}