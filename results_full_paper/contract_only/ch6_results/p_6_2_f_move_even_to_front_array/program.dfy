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

method p_6_2_f_move_even_to_front_array(inputs: array<int>) returns (result: array<int>)
	ensures result[..] == evens(inputs[..]) + odds(inputs[..])
{
  var i := inputs.Length;
  var es: seq<int> := [];
  var os: seq<int> := [];

  while i > 0
    invariant 0 <= i <= inputs.Length
    invariant es == evens(inputs[i..])
    invariant os == odds(inputs[i..])
    decreases i
  {
    i := i - 1;
    assert 0 <= i < inputs.Length;
    assert es == evens(inputs[i + 1..]);
    assert os == odds(inputs[i + 1..]);
    assert |inputs[i..]| > 0;
    assert inputs[i..][0] == inputs[i];
    assert inputs[i..][1..] == inputs[i + 1..];

    if inputs[i] % 2 == 0 {
      assert inputs[i..][0] % 2 == 0;
      assert evens(inputs[i..]) == [inputs[i]] + evens(inputs[i + 1..]);
      assert odds(inputs[i..]) == odds(inputs[i + 1..]);
      es := [inputs[i]] + es;
      assert es == evens(inputs[i..]);
      assert os == odds(inputs[i..]);
    } else {
      assert inputs[i..][0] % 2 != 0;
      assert evens(inputs[i..]) == evens(inputs[i + 1..]);
      assert odds(inputs[i..]) == [inputs[i]] + odds(inputs[i + 1..]);
      os := [inputs[i]] + os;
      assert es == evens(inputs[i..]);
      assert os == odds(inputs[i..]);
    }
  }

  var out := es + os;
  assert i == 0;
  assert inputs[i..] == inputs[..];
  assert out == evens(inputs[..]) + odds(inputs[..]);

  result := new int[|out|](j => if 0 <= j < |out| then out[j] else 0);
  assert |result[..]| == |out|;
  assert forall j :: 0 <= j < |out| ==> result[..][j] == out[j];
  assert result[..] == out;
}