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
  var i := |inputs|;
  var evenPart: seq<int> := [];
  var oddPart: seq<int> := [];

  assert inputs[|inputs|..] == [];
  assert evens(inputs[|inputs|..]) == [];
  assert odds(inputs[|inputs|..]) == [];

  while i > 0
    invariant 0 <= i <= |inputs|
    invariant evenPart == evens(inputs[i..])
    invariant oddPart == odds(inputs[i..])
    decreases i
  {
    i := i - 1;

    assert 0 <= i < |inputs|;
    assert |inputs[i..]| > 0;
    assert inputs[i..][0] == inputs[i];
    assert inputs[i..][1..] == inputs[i + 1..];

    if inputs[i] % 2 == 0 {
      assert evens(inputs[i..]) == [inputs[i]] + evens(inputs[i + 1..]);
      assert odds(inputs[i..]) == odds(inputs[i + 1..]);
      evenPart := [inputs[i]] + evenPart;
      assert evenPart == evens(inputs[i..]);
      assert oddPart == odds(inputs[i..]);
    } else {
      assert evens(inputs[i..]) == evens(inputs[i + 1..]);
      assert odds(inputs[i..]) == [inputs[i]] + odds(inputs[i + 1..]);
      oddPart := [inputs[i]] + oddPart;
      assert evenPart == evens(inputs[i..]);
      assert oddPart == odds(inputs[i..]);
    }
  }

  assert i == 0;
  result := evenPart + oddPart;
}