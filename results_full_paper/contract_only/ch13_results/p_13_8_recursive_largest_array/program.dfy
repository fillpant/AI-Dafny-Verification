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
  var i := inputs.Length - 1;
  largest := inputs[i];

  var init := inputs[i..];
  assert |init| == 1;
  assert init[0] == inputs[i];
  assert find_largest(init) == inputs[i];
  assert largest == find_largest(inputs[i..]);

  while i > 0
    invariant 0 <= i < inputs.Length
    invariant largest == find_largest(inputs[i..])
    decreases i
  {
    var subLargest := largest;
    i := i - 1;

    assert 0 <= i < inputs.Length;
    assert i + 1 < inputs.Length;
    assert subLargest == find_largest(inputs[i + 1..]);

    var s := inputs[i..];
    assert |s| > 1;
    assert s == [s[0]] + s[1..];
    assert s[0] == inputs[i];
    assert s[1..] == inputs[i + 1..];
    assert find_largest(s) == (if s[0] >= find_largest(s[1..]) then s[0] else find_largest(s[1..]));
    assert find_largest(inputs[i..]) == (if inputs[i] >= subLargest then inputs[i] else subLargest);

    if inputs[i] >= subLargest {
      largest := inputs[i];
    } else {
      largest := subLargest;
    }

    assert largest == (if inputs[i] >= subLargest then inputs[i] else subLargest);
    assert largest == find_largest(inputs[i..]);
  }

  assert i == 0;
  assert inputs[i..] == inputs[..];
  assert largest == find_largest(inputs[..]);
}