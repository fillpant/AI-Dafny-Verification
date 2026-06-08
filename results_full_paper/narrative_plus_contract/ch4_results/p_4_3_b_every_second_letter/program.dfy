method p_4_3_b_every_second_letter(s: string) returns (result: string)
	ensures |result| * 2 == |s| || |result| * 2 + 1 == |s|
	ensures forall i :: 0 <= i < |result| ==> result[i] == s[2 * i]
{
  result := "";
  var pos := 0;

  while pos + 1 < |s|
    invariant 0 <= pos <= |s|
    invariant |result| * 2 == pos
    invariant forall i :: 0 <= i < |result| ==> result[i] == s[2 * i]
    decreases |s| - pos
  {
    var prev := result;
    var oldLen := |result|;
    var oldPos := pos;

    assert oldLen * 2 == oldPos;
    assert oldPos + 1 < |s|;
    assert oldPos + 2 <= |s|;
    assert |prev| == oldLen;

    result := prev + s[oldPos..oldPos + 1];
    pos := oldPos + 2;

    assert |s[oldPos..oldPos + 1]| == 1;
    assert s[oldPos..oldPos + 1][0] == s[oldPos];
    assert |result| == oldLen + 1;
    assert |result| * 2 == pos;

    forall i | 0 <= i < |result|
      ensures result[i] == s[2 * i]
    {
      if i < oldLen {
        assert i < |prev|;
        assert result[i] == prev[i];
        assert prev[i] == s[2 * i];
      } else {
        assert i == oldLen;
        assert result[i] == s[oldPos..oldPos + 1][0];
        assert result[i] == s[oldPos];
        assert oldPos == 2 * i;
      }
    }
  }

  if pos == |s| {
    assert |result| * 2 == |s|;
  } else {
    assert pos < |s|;
    assert pos + 1 <= |s|;
    assert |s| <= pos + 1;
    assert pos + 1 == |s|;
    assert |result| * 2 + 1 == |s|;
  }
}