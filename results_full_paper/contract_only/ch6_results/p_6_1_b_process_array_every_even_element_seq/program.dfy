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
  var r10: seq<int> := [];
  assert inputs[10..] == [];
  assert r10 == evens(inputs[10..]);

  var r9: seq<int> := if inputs[9] % 2 == 0 then [inputs[9]] + r10 else r10;
  assert |inputs[9..]| == 1;
  assert (inputs[9..])[0] == inputs[9];
  assert (inputs[9..])[1..] == inputs[10..];
  assert r9 == evens(inputs[9..]);

  var r8: seq<int> := if inputs[8] % 2 == 0 then [inputs[8]] + r9 else r9;
  assert |inputs[8..]| == 2;
  assert (inputs[8..])[0] == inputs[8];
  assert (inputs[8..])[1..] == inputs[9..];
  assert r8 == evens(inputs[8..]);

  var r7: seq<int> := if inputs[7] % 2 == 0 then [inputs[7]] + r8 else r8;
  assert |inputs[7..]| == 3;
  assert (inputs[7..])[0] == inputs[7];
  assert (inputs[7..])[1..] == inputs[8..];
  assert r7 == evens(inputs[7..]);

  var r6: seq<int> := if inputs[6] % 2 == 0 then [inputs[6]] + r7 else r7;
  assert |inputs[6..]| == 4;
  assert (inputs[6..])[0] == inputs[6];
  assert (inputs[6..])[1..] == inputs[7..];
  assert r6 == evens(inputs[6..]);

  var r5: seq<int> := if inputs[5] % 2 == 0 then [inputs[5]] + r6 else r6;
  assert |inputs[5..]| == 5;
  assert (inputs[5..])[0] == inputs[5];
  assert (inputs[5..])[1..] == inputs[6..];
  assert r5 == evens(inputs[5..]);

  var r4: seq<int> := if inputs[4] % 2 == 0 then [inputs[4]] + r5 else r5;
  assert |inputs[4..]| == 6;
  assert (inputs[4..])[0] == inputs[4];
  assert (inputs[4..])[1..] == inputs[5..];
  assert r4 == evens(inputs[4..]);

  var r3: seq<int> := if inputs[3] % 2 == 0 then [inputs[3]] + r4 else r4;
  assert |inputs[3..]| == 7;
  assert (inputs[3..])[0] == inputs[3];
  assert (inputs[3..])[1..] == inputs[4..];
  assert r3 == evens(inputs[3..]);

  var r2: seq<int> := if inputs[2] % 2 == 0 then [inputs[2]] + r3 else r3;
  assert |inputs[2..]| == 8;
  assert (inputs[2..])[0] == inputs[2];
  assert (inputs[2..])[1..] == inputs[3..];
  assert r2 == evens(inputs[2..]);

  var r1: seq<int> := if inputs[1] % 2 == 0 then [inputs[1]] + r2 else r2;
  assert |inputs[1..]| == 9;
  assert (inputs[1..])[0] == inputs[1];
  assert (inputs[1..])[1..] == inputs[2..];
  assert r1 == evens(inputs[1..]);

  var r0: seq<int> := if inputs[0] % 2 == 0 then [inputs[0]] + r1 else r1;
  assert |inputs[0..]| == 10;
  assert inputs[0..] == inputs;
  assert (inputs[0..])[0] == inputs[0];
  assert (inputs[0..])[1..] == inputs[1..];
  assert r0 == evens(inputs[0..]);

  even_elements := r0;
  assert even_elements == evens(inputs);
}