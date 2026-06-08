function evens(inputs: seq<int>): seq<int>
{
  if inputs ==[] then []
  else if inputs[0] % 2 == 0 then [inputs[0]] + evens(inputs[1..])
  else evens(inputs[1..])
}

method p_6_1_b_process_array_every_even_element_seq(inputs: seq<int>) returns (even_elements: seq<int>)
	requires |inputs| == 10
	ensures even_elements == evens(inputs)
{
  even_elements := [];
  var i := 0;

  assert inputs[0..] == inputs;
  assert even_elements + evens(inputs[i..]) == evens(inputs);

  while i < |inputs|
    invariant 0 <= i <= |inputs|
    invariant even_elements + evens(inputs[i..]) == evens(inputs)
    decreases |inputs| - i
  {
    assert inputs[i..] != [];
    assert (inputs[i..])[0] == inputs[i];
    assert (inputs[i..])[1..] == inputs[i + 1..];

    if inputs[i] % 2 == 0 {
      assert evens(inputs[i..]) == [inputs[i]] + evens(inputs[i + 1..]);
      var prev := even_elements;
      assert prev + evens(inputs[i..]) == evens(inputs);
      even_elements := even_elements + [inputs[i]];
      assert even_elements == prev + [inputs[i]];
      assert even_elements + evens(inputs[i + 1..]) == prev + ([inputs[i]] + evens(inputs[i + 1..]));
      assert prev + ([inputs[i]] + evens(inputs[i + 1..])) == prev + evens(inputs[i..]);
      assert even_elements + evens(inputs[i + 1..]) == evens(inputs);
    } else {
      assert evens(inputs[i..]) == evens(inputs[i + 1..]);
      assert even_elements + evens(inputs[i + 1..]) == evens(inputs);
    }

    i := i + 1;
  }

  assert i == |inputs|;
  assert inputs[i..] == [];
  assert evens(inputs[i..]) == [];
  assert even_elements == even_elements + [];
  assert even_elements == evens(inputs);
}