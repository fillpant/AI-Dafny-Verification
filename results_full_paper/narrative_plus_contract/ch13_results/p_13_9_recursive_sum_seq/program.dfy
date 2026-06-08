function sum_array(inputs: seq<int>): int
  ensures sum_array(inputs) == (if |inputs| == 0 then 0 else inputs[0] + sum_array(inputs[1..]))
{
  if |inputs| == 0 then 0
  else inputs[0] + sum_array(inputs[1..])
}

method p_13_9_recursive_sum_seq(inputs: seq<int>) returns (sum: int)
	ensures sum == sum_array(inputs)
{
  if |inputs| == 0 {
    sum := 0;
  } else {
    var tailSum := p_13_9_recursive_sum_seq(inputs[1..]);
    sum := inputs[0] + tailSum;
  }
}