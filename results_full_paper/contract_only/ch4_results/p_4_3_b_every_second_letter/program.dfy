method p_4_3_b_every_second_letter(s: string) returns (result: string)
	ensures |result| * 2 == |s| || |result| * 2 + 1 == |s|
	ensures forall i :: 0 <= i < |result| ==> result[i] == s[2 * i]
{
  result := "";
  var k := 0;

  while k + 1 < |s|
    invariant 0 <= k <= |s|
    invariant k == 2 * |result|
    invariant forall i :: 0 <= i < |result| ==> result[i] == s[2 * i]
    decreases |s| - k
  {
    var oldResult := result;
    var oldK := k;

    assert forall i :: 0 <= i < |oldResult| ==> oldResult[i] == s[2 * i];
    assert oldK + 1 <= |s|;

    result := oldResult + s[oldK..oldK + 1];

    assert |s[oldK..oldK + 1]| == 1;
    assert |result| == |oldResult| + 1;
    assert result[|oldResult|] == (s[oldK..oldK + 1])[0];
    assert (s[oldK..oldK + 1])[0] == s[oldK];
    assert result[|oldResult|] == s[oldK];

    assert forall i :: 0 <= i < |result| ==> result[i] == s[2 * i] by {
      forall i | 0 <= i < |result|
        ensures result[i] == s[2 * i]
      {
        if i < |oldResult| {
          assert result[i] == oldResult[i];
          assert oldResult[i] == s[2 * i];
        } else {
          assert i == |oldResult|;
          assert oldK == 2 * |oldResult|;
          assert oldK == 2 * i;
          assert result[i] == s[oldK];
        }
      }
    }

    k := oldK + 2;
    assert k == 2 * |result|;
    assert k <= |s|;
  }

  assert |s| <= k + 1;
  if k == |s| {
    assert |result| * 2 == |s|;
  } else {
    assert k < |s|;
    assert k + 1 == |s|;
    assert |result| * 2 + 1 == |s|;
  }
}