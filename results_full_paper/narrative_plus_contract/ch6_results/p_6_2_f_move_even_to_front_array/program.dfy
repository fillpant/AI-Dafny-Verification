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
  var n := inputs.Length;
  var es: seq<int> := [];
  var os: seq<int> := [];
  var i := n;

  assert inputs[n..] == [];
  assert evens(inputs[n..]) == [];
  assert odds(inputs[n..]) == [];

  while 0 < i
    invariant 0 <= i <= n
    invariant es == evens(inputs[i..])
    invariant os == odds(inputs[i..])
  {
    var oldI := i;
    var k := i - 1;
    var x := inputs[k];
    ghost var tail := inputs[oldI..];
    ghost var whole := inputs[k..];

    assert 0 <= k < n;
    assert oldI == k + 1;
    assert inputs[k..oldI] == [x];
    assert whole == inputs[k..oldI] + tail;
    assert whole == [x] + tail;
    assert |whole| != 0;
    assert whole[0] == x;
    assert whole[1..] == tail;

    if x % 2 == 0 {
      es := [x] + es;
      assert evens(whole) == [x] + evens(tail);
      assert odds(whole) == odds(tail);
      assert es == evens(inputs[k..]);
      assert os == odds(inputs[k..]);
    } else {
      os := [x] + os;
      assert evens(whole) == evens(tail);
      assert odds(whole) == [x] + odds(tail);
      assert es == evens(inputs[k..]);
      assert os == odds(inputs[k..]);
    }

    i := k;
  }

  assert i == 0;
  assert inputs[i..] == inputs[..];
  assert es == evens(inputs[..]);
  assert os == odds(inputs[..]);

  var combined := es + os;
  var m := |combined|;
  result := new int[m];

  var j := 0;
  while j < m
    invariant 0 <= j <= m
    invariant result.Length == m
    invariant forall t :: 0 <= t < j ==> result[t] == combined[t]
  {
    result[j] := combined[j];
    j := j + 1;
  }

  assert j == m;
  assert forall t :: 0 <= t < m ==> result[t] == combined[t];
  assert |result[..]| == m;
  forall t | 0 <= t < m
    ensures result[..][t] == combined[t]
  {
    assert result[..][t] == result[t];
  }
  assert forall t :: 0 <= t < |result[..]| ==> result[..][t] == combined[t];
  assert result[..] == combined;
  assert combined == es + os;
  assert combined == evens(inputs[..]) + odds(inputs[..]);
}