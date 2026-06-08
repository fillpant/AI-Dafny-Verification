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
  var r: seq<int> := [];
  var k := inputs.Length;
  assert k == 10;
  assert inputs[k..] == [];
  assert r == evens(inputs[k..]);

  while k > 0
    invariant inputs.Length == 10
    invariant 0 <= k <= inputs.Length
    invariant r == evens(inputs[k..])
  {
    k := k - 1;
    assert 0 <= k < inputs.Length;
    assert 0 <= k + 1 <= inputs.Length;

    var tail := r;
    assert tail == evens(inputs[k + 1..]);

    var current := inputs[k..];
    assert current != [];
    assert current[0] == inputs[k];
    assert current[1..] == inputs[k + 1..];

    if inputs[k] % 2 == 0 {
      assert current[0] % 2 == 0;
      assert evens(current) == [current[0]] + evens(current[1..]);
      r := [inputs[k]] + tail;
      assert [current[0]] == [inputs[k]];
      assert evens(current[1..]) == tail;
      assert r == evens(current);
    } else {
      assert current[0] % 2 != 0;
      assert evens(current) == evens(current[1..]);
      r := tail;
      assert evens(current[1..]) == tail;
      assert r == evens(current);
    }
    assert current == inputs[k..];
    assert r == evens(inputs[k..]);
  }

  assert k == 0;
  assert inputs[k..] == inputs[..];
  assert r == evens(inputs[..]);

  even_elements := new int[|r|](i => if 0 <= i < |r| then r[i] else 0);
  assert even_elements.Length == |r|;

  forall j | 0 <= j < |r|
    ensures even_elements[..][j] == r[j]
  {
    assert even_elements[j] == r[j];
    assert even_elements[..][j] == even_elements[j];
  }

  assert |even_elements[..]| == |r|;
  assert even_elements[..] == r;
  assert even_elements[..] == evens(inputs[..]);
}