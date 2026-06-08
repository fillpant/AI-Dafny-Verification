method p_6_1_a_process_array_even_indexed_array(inputs: array<int>) returns (even_indexed: array<int>)
	requires inputs.Length == 10
	ensures even_indexed[..] == [inputs[0], inputs[2], inputs[4], inputs[6], inputs[8]]
{
  even_indexed := new int[5];
  even_indexed[0] := inputs[0];
  even_indexed[1] := inputs[2];
  even_indexed[2] := inputs[4];
  even_indexed[3] := inputs[6];
  even_indexed[4] := inputs[8];
}