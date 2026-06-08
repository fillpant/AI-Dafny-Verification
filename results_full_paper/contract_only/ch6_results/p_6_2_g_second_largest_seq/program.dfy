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
  var i := 1;
  second_largest := inputs[0];

  while i < |inputs|
    invariant 1 <= i <= |inputs|
    invariant second_largest in inputs[..i]
    invariant forall x {:trigger x in inputs[..i]} :: x in inputs[..i] ==> x <= second_largest
    decreases |inputs| - i
  {
    var oldSecond := second_largest;

    if inputs[i] > oldSecond {
      second_largest := inputs[i];
    }

    assert inputs[..i + 1] == inputs[..i] + [inputs[i]];

    assert second_largest in inputs[..i + 1] by {
      if inputs[i] > oldSecond {
        assert second_largest == inputs[i];
        assert second_largest in [inputs[i]];
        assert second_largest in inputs[..i] + [inputs[i]];
      } else {
        assert second_largest == oldSecond;
        assert second_largest in inputs[..i];
        assert second_largest in inputs[..i] + [inputs[i]];
      }
    }

    assert forall x {:trigger x in inputs[..i + 1]} :: x in inputs[..i + 1] ==> x <= second_largest by {
      forall x {:trigger x in inputs[..i + 1]} | x in inputs[..i + 1]
        ensures x <= second_largest
      {
        assert x in inputs[..i] + [inputs[i]];
        if x in inputs[..i] {
          assert x <= oldSecond;
          if inputs[i] > oldSecond {
            assert oldSecond < second_largest;
          } else {
            assert second_largest == oldSecond;
          }
        } else {
          assert x in [inputs[i]];
          assert x == inputs[i];
          if inputs[i] > oldSecond {
            assert second_largest == inputs[i];
          } else {
            assert second_largest == oldSecond;
            assert inputs[i] <= second_largest;
          }
        }
      }
    }

    i := i + 1;
  }

  assert inputs[..i] == inputs;
  assert second_largest in inputs;
  assert forall x {:trigger x in inputs} :: x in inputs ==> x <= second_largest;
}