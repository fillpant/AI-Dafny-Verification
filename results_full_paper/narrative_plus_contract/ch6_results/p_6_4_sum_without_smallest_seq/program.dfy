function find_smallest(inputs: seq<int>): (ret: int)
  requires |inputs| >= 1
  ensures forall x :: x in inputs ==> ret <= x 
{
  if |inputs| == 1 then inputs[0]
  else 
    assert 2 <= |inputs|;
    var rest_smallest := find_smallest(inputs[1..]);
    var ret: int := if inputs[0] <= rest_smallest then inputs[0] else rest_smallest;
    assert inputs == [inputs[0]] + inputs[1..]; 
    assert ret == if inputs[0] <= rest_smallest then inputs[0] else rest_smallest;
    ret 
}

function sum_array(inputs: seq<int>): int
{
  if |inputs| == 0 then 0
  else  inputs[0] + sum_array(inputs[1..])
}

method p_6_4_sum_without_smallest_seq(inputs: seq<int>) returns (sum: int)
	requires |inputs| >= 1
	ensures sum == sum_array(inputs) - find_smallest(inputs)
{
  var i: int := |inputs| - 1;
  assert 0 <= i < |inputs|;

  var runningSum: int := inputs[i];
  var smallest: int := inputs[i];

  assert |inputs[i..]| == 1;
  assert (inputs[i..])[0] == inputs[i];
  assert sum_array(inputs[i..]) == inputs[i];
  assert find_smallest(inputs[i..]) == inputs[i];

  while 0 < i
    invariant 0 <= i < |inputs|
    invariant runningSum == sum_array(inputs[i..])
    invariant smallest == find_smallest(inputs[i..])
    decreases i
  {
    var oldI: int := i;
    i := i - 1;

    assert oldI == i + 1;
    assert 0 <= i;
    assert i + 1 < |inputs|;
    assert runningSum == sum_array(inputs[i + 1..]);
    assert smallest == find_smallest(inputs[i + 1..]);

    assert |inputs[i..]| >= 2;
    assert (inputs[i..])[0] == inputs[i];
    assert (inputs[i..])[1..] == inputs[i + 1..];

    assert sum_array(inputs[i..]) == (inputs[i..])[0] + sum_array((inputs[i..])[1..]);
    assert sum_array(inputs[i..]) == inputs[i] + sum_array(inputs[i + 1..]);

    assert find_smallest(inputs[i..]) ==
      (if (inputs[i..])[0] <= find_smallest((inputs[i..])[1..]) then (inputs[i..])[0] else find_smallest((inputs[i..])[1..]));
    assert find_smallest(inputs[i..]) ==
      (if inputs[i] <= find_smallest(inputs[i + 1..]) then inputs[i] else find_smallest(inputs[i + 1..]));

    runningSum := inputs[i] + runningSum;
    assert runningSum == inputs[i] + sum_array(inputs[i + 1..]);
    assert runningSum == sum_array(inputs[i..]);

    if inputs[i] <= smallest {
      assert inputs[i] <= find_smallest(inputs[i + 1..]);
      smallest := inputs[i];
    } else {
      assert !(inputs[i] <= find_smallest(inputs[i + 1..]));
    }
    assert smallest ==
      (if inputs[i] <= find_smallest(inputs[i + 1..]) then inputs[i] else find_smallest(inputs[i + 1..]));
    assert smallest == find_smallest(inputs[i..]);
  }

  assert i == 0;
  assert inputs[i..] == inputs;
  assert runningSum == sum_array(inputs);
  assert smallest == find_smallest(inputs);
  sum := runningSum - smallest;
}