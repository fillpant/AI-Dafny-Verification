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
  var i := |inputs| - 1;
  assert 0 <= i < |inputs|;
  var smallest := inputs[i];
  sum := 0;

  assert i + 1 == |inputs|;
  assert inputs[i..] == [smallest];
  assert find_smallest(inputs[i..]) == smallest;
  assert sum_array(inputs[i..]) == smallest;

  while 0 < i
    invariant 0 <= i < |inputs|
    invariant smallest == find_smallest(inputs[i..])
    invariant sum == sum_array(inputs[i..]) - smallest
    decreases i
  {
    var oldI := i;
    var j := oldI - 1;
    assert 0 <= j < oldI < |inputs|;
    var x := inputs[j];
    var oldSmallest := smallest;
    var oldSum := sum;

    assert oldSmallest == find_smallest(inputs[oldI..]);
    assert oldSum == sum_array(inputs[oldI..]) - oldSmallest;
    assert oldI == j + 1;
    assert inputs[j..oldI] == [x];
    assert inputs[j..] == inputs[j..oldI] + inputs[oldI..];
    assert inputs[j..] == [x] + inputs[oldI..];
    assert (inputs[j..])[0] == x;
    assert (inputs[j..])[1..] == inputs[oldI..];
    assert 2 <= |inputs[j..]|;
    assert sum_array(inputs[j..]) == x + sum_array(inputs[oldI..]);

    if x <= oldSmallest {
      assert find_smallest(inputs[j..]) == x;
      sum := oldSum + oldSmallest;
      smallest := x;
      assert sum == sum_array(inputs[oldI..]);
      assert sum == sum_array(inputs[j..]) - smallest;
    } else {
      assert oldSmallest < x;
      assert find_smallest(inputs[j..]) == oldSmallest;
      sum := oldSum + x;
      smallest := oldSmallest;
      assert sum == sum_array(inputs[j..]) - smallest;
    }

    i := j;
    assert smallest == find_smallest(inputs[i..]);
    assert sum == sum_array(inputs[i..]) - smallest;
  }

  assert i == 0;
  assert inputs[i..] == inputs;
  assert sum == sum_array(inputs) - find_smallest(inputs);
}