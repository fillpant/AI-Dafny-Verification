method p_13_3_recursive_reverse_string(text: string) returns (reversed: string)
	ensures |reversed| == |text|
	ensures forall i :: 0 <= i < |text| ==> reversed[i] == text[|text| - 1 - i]
{
  reversed := "";
  var i := 0;
  while i < |text|
    invariant 0 <= i <= |text|
    invariant |reversed| == i
    invariant forall j :: 0 <= j < i ==> reversed[j] == text[i - 1 - j]
  {
    assert 0 <= i < |text|;
    var prev := reversed;
    reversed := text[i..i+1] + prev;
    assert |text[i..i+1]| == 1;
    assert (text[i..i+1])[0] == text[i];
    assert |reversed| == i + 1;

    forall j | 0 <= j < i + 1
      ensures reversed[j] == text[i - j]
    {
      if j == 0 {
        assert reversed[j] == (text[i..i+1])[0];
        assert (text[i..i+1])[0] == text[i];
        assert i - j == i;
        assert reversed[j] == text[i - j];
      } else {
        assert 0 <= j - 1 < i;
        assert reversed[j] == prev[j - 1];
        assert prev[j - 1] == text[i - 1 - (j - 1)];
        assert i - 1 - (j - 1) == i - j;
        assert reversed[j] == text[i - j];
      }
    }

    i := i + 1;
  }
}