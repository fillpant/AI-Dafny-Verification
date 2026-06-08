function evens(inputs: seq<int>): seq<int>
{
  if inputs ==[] then []
  else if inputs[0] % 2 == 0 then [inputs[0]] + evens(inputs[1..])
  else evens(inputs[1..])
}

method p_6_1_b_process_array_every_even_element_array(inputs: array<int>) returns (even_elements: array<int>)
	requires inputs.Length == 10
	ensures even_elements[..] == evens(inputs[..])
{
  var s: seq<int> := [];
  var i: int := inputs.Length;

  assert inputs[i..] == [];
  assert evens(inputs[i..]) == [];

  while i > 0
    invariant 0 <= i <= inputs.Length
    invariant s == evens(inputs[i..])
  {
    i := i - 1;
    assert 0 <= i < inputs.Length;
    assert i + 1 <= inputs.Length;
    assert s == evens(inputs[i + 1..]);

    assert inputs[i..] != [];
    assert (inputs[i..])[0] == inputs[i];
    assert (inputs[i..])[1..] == inputs[i + 1..];

    if inputs[i] % 2 == 0 {
      assert evens(inputs[i..]) == [inputs[i]] + evens(inputs[i + 1..]);
      s := [inputs[i]] + s;
      assert s == [inputs[i]] + evens(inputs[i + 1..]);
      assert s == evens(inputs[i..]);
    } else {
      assert evens(inputs[i..]) == evens(inputs[i + 1..]);
      assert s == evens(inputs[i..]);
    }
  }

  assert i == 0;
  assert inputs[0..] == inputs[..];
  assert s == evens(inputs[..]);

  even_elements := new int[|s|](j => if 0 <= j < |s| then s[j] else 0);

  assert even_elements.Length == |s|;
  assert forall j :: 0 <= j < |s| ==> even_elements[j] == s[j];
  assert forall j :: 0 <= j < |s| ==> even_elements[..][j] == s[j];
  assert even_elements[..] == s;
}