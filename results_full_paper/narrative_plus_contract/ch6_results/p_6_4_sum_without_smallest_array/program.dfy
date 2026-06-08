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

method p_6_4_sum_without_smallest_array(inputs: array<int>) returns (sum: int)
	requires inputs.Length >= 1
	ensures sum == sum_array(inputs[..]) - find_smallest(inputs[..])
{
  var i := inputs.Length - 1;
  var total := inputs[i];
  var smallest := inputs[i];

  assert 0 <= i < inputs.Length;
  assert |inputs[i..]| == 1;
  assert inputs[i..][0] == inputs[i];
  assert sum_array(inputs[i..]) == inputs[i];
  assert find_smallest(inputs[i..]) == inputs[i];

  while i > 0
    invariant 0 <= i < inputs.Length
    invariant total == sum_array(inputs[i..])
    invariant smallest == find_smallest(inputs[i..])
  {
    var j := i - 1;
    assert 0 <= j < inputs.Length;
    assert i == j + 1;
    assert |inputs[j..]| >= 2;
    assert inputs[j..][0] == inputs[j];
    assert inputs[j..][1..] == inputs[i..];

    assert sum_array(inputs[j..]) == inputs[j] + sum_array(inputs[i..]);
    assert find_smallest(inputs[j..]) ==
      (if inputs[j] <= find_smallest(inputs[i..]) then inputs[j] else find_smallest(inputs[i..]));

    total := inputs[j] + total;
    assert total == sum_array(inputs[j..]);

    if inputs[j] <= smallest {
      assert inputs[j] <= find_smallest(inputs[i..]);
      smallest := inputs[j];
    } else {
      assert !(inputs[j] <= find_smallest(inputs[i..]));
    }
    assert smallest == find_smallest(inputs[j..]);

    i := j;
  }

  assert i == 0;
  assert inputs[i..] == inputs[..];
  assert total == sum_array(inputs[..]);
  assert smallest == find_smallest(inputs[..]);
  sum := total - smallest;
}