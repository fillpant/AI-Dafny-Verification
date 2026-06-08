method p_13_3_recursive_reverse_string(text: string) returns (reversed: string)
	ensures |reversed| == |text|
	ensures forall i :: 0 <= i < |text| ==> reversed[i] == text[|text| - 1 - i]
{
  if |text| == 0 {
    reversed := "";
  } else {
    var rest := text[1..];
    var restReversed := p_13_3_recursive_reverse_string(rest);
    reversed := restReversed + text[0..1];

    assert |rest| == |text| - 1;
    assert |text[0..1]| == 1;
    assert |restReversed| == |rest|;
    assert |reversed| == |text|;

    forall i | 0 <= i < |text|
      ensures reversed[i] == text[|text| - 1 - i]
    {
      if i < |text| - 1 {
        assert i < |restReversed|;
        assert reversed[i] == restReversed[i];
        assert restReversed[i] == rest[|rest| - 1 - i];
        assert 0 <= |rest| - 1 - i < |rest|;
        assert rest[|rest| - 1 - i] == text[1 + (|rest| - 1 - i)];
        assert 1 + (|rest| - 1 - i) == |text| - 1 - i;
      } else {
        assert i == |text| - 1;
        assert i == |restReversed|;
        assert reversed[i] == text[0..1][0];
        assert text[0..1][0] == text[0];
        assert |text| - 1 - i == 0;
      }
    }
  }
}