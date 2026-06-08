method p_6_1_c_process_array_reverse_order_seq(inputs: seq<int>) returns (reversed: seq<int>)
	requires |inputs| == 10
	ensures |reversed| == |inputs|
	ensures forall i :: 0 <= i < |reversed| ==> reversed[i] == inputs[|inputs| - 1 - i]
{
  reversed := [inputs[9], inputs[8], inputs[7], inputs[6], inputs[5], inputs[4], inputs[3], inputs[2], inputs[1], inputs[0]];

  assert forall i :: 0 <= i < |reversed| ==> reversed[i] == inputs[|inputs| - 1 - i] by {
    forall i | 0 <= i < |reversed|
      ensures reversed[i] == inputs[|inputs| - 1 - i]
    {
      if i == 0 {
        assert |inputs| - 1 - i == 9;
      } else if i == 1 {
        assert |inputs| - 1 - i == 8;
      } else if i == 2 {
        assert |inputs| - 1 - i == 7;
      } else if i == 3 {
        assert |inputs| - 1 - i == 6;
      } else if i == 4 {
        assert |inputs| - 1 - i == 5;
      } else if i == 5 {
        assert |inputs| - 1 - i == 4;
      } else if i == 6 {
        assert |inputs| - 1 - i == 3;
      } else if i == 7 {
        assert |inputs| - 1 - i == 2;
      } else if i == 8 {
        assert |inputs| - 1 - i == 1;
      } else {
        assert i == 9;
        assert |inputs| - 1 - i == 0;
      }
    }
  }
}