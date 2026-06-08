method p_6_1_c_process_array_reverse_order_seq(inputs: seq<int>) returns (reversed: seq<int>)
	requires |inputs| == 10
	ensures |reversed| == |inputs|
	ensures forall i :: 0 <= i < |reversed| ==> reversed[i] == inputs[|inputs| - 1 - i]
{
  reversed := seq(|inputs|, i requires 0 <= i < |inputs| => inputs[|inputs| - 1 - i]);
}