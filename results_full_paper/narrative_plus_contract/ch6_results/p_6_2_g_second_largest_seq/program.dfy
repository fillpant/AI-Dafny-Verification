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

method p_6_2_g_second_largest_seq(inputs: seq<int>) returns (second_largest: int)
	requires |inputs| >= 2
	ensures second_largest <= find_largest(inputs)
	ensures forall x :: x in inputs ==> x < find_largest(inputs) ==> x <= second_largest
{
  var i: int := 1;
  var largest: int := inputs[0];
  var maxIdx: int := 0;

  while i < |inputs|
    invariant 1 <= i <= |inputs|
    invariant 0 <= maxIdx < i
    invariant largest == inputs[maxIdx]
    invariant forall j: int :: 0 <= j < i ==> inputs[j] <= largest
  {
    var oldLargest := largest;

    if inputs[i] > largest {
      largest := inputs[i];
      maxIdx := i;
      assert oldLargest <= largest;
      assert inputs[i] <= largest;
    } else {
      assert inputs[i] <= largest;
      assert oldLargest == largest;
      assert oldLargest <= largest;
    }

    assert oldLargest <= largest;
    assert inputs[i] <= largest;

    forall j: int | 0 <= j < i + 1
      ensures inputs[j] <= largest
    {
      if j < i {
        assert inputs[j] <= oldLargest;
        assert oldLargest <= largest;
      } else {
        assert j == i;
        assert inputs[j] <= largest;
      }
    }

    i := i + 1;
  }

  second_largest := largest;

  assert 0 <= maxIdx < |inputs|;
  assert second_largest == inputs[maxIdx];
  assert second_largest in inputs;

  forall x: int | x in inputs
    ensures x <= second_largest
  {
    var j: int :| 0 <= j < |inputs| && inputs[j] == x;
    assert inputs[j] <= second_largest;
    assert x == inputs[j];
  }
}