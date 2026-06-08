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

method p_13_8_recursive_largest_seq(inputs: seq<int>) returns (largest: int)
	requires |inputs| >= 1
	ensures largest == find_largest(inputs)
{
  if |inputs| == 1 {
    largest := inputs[0];
  } else {
    assert |inputs[1..]| >= 1;
    var sub_largest := p_13_8_recursive_largest_seq(inputs[1..]);
    assert inputs == [inputs[0]] + inputs[1..];
    if inputs[0] >= sub_largest {
      largest := inputs[0];
    } else {
      largest := sub_largest;
    }
  }
}