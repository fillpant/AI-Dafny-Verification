method p_6_1_d_process_array_first_and_last_array(inputs: array<int>) returns (first_and_last: array<int>)
	requires inputs.Length == 10
	ensures first_and_last[..] == [inputs[0], inputs[inputs.Length - 1]]
{
  first_and_last := new int[2];
  first_and_last[0] := inputs[0];
  first_and_last[1] := inputs[inputs.Length - 1];
}