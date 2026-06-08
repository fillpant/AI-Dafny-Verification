function evens(s: seq<int>): seq<int>
{
  if |s| == 0 then []
  else if s[0] % 2 == 0
       then [s[0]] + evens(s[1..])
       else evens(s[1..])
}

function odds(s: seq<int>): seq<int>
{
  if |s| == 0 then []
  else if s[0] % 2 != 0
       then [s[0]] + odds(s[1..])
       else odds(s[1..])
}

method p_6_2_f_move_even_to_front_seq(inputs: seq<int>) returns (result: seq<int>)
	ensures result == evens(inputs) + odds(inputs)
{
  var es: seq<int> := [];
  var os: seq<int> := [];
  var i := |inputs|;

  while i > 0
    invariant 0 <= i <= |inputs|
    invariant es == evens(inputs[i..])
    invariant os == odds(inputs[i..])
  {
    i := i - 1;

    assert 0 <= i && i < |inputs|;
    assert inputs[i..i+1] == [inputs[i]];
    assert inputs[i..] == inputs[i..i+1] + inputs[i+1..];
    assert inputs[i..] == [inputs[i]] + inputs[i+1..];
    assert (inputs[i..])[0] == inputs[i];
    assert (inputs[i..])[1..] == inputs[i+1..];

    if inputs[i] % 2 == 0 {
      assert evens(inputs[i..]) == [inputs[i]] + evens(inputs[i+1..]);
      assert odds(inputs[i..]) == odds(inputs[i+1..]);
      es := [inputs[i]] + es;
    } else {
      assert evens(inputs[i..]) == evens(inputs[i+1..]);
      assert odds(inputs[i..]) == [inputs[i]] + odds(inputs[i+1..]);
      os := [inputs[i]] + os;
    }

    assert es == evens(inputs[i..]);
    assert os == odds(inputs[i..]);
  }

  assert i == 0;
  assert inputs[i..] == inputs;
  assert es == evens(inputs);
  assert os == odds(inputs);
  result := es + os;
}