method p_4_3_a_extract_uppercase(s: string) returns (uppercase: string)
	ensures forall c :: c in uppercase ==> 'A' <= c <= 'Z'
	ensures forall c :: c in s && 'A' <= c <= 'Z' ==> c in uppercase
{
  uppercase := "";
  var i := 0;
  while i < |s|
    invariant 0 <= i <= |s|
    invariant forall c :: c in uppercase ==> 'A' <= c <= 'Z'
    invariant forall j :: 0 <= j < i && 'A' <= s[j] <= 'Z' ==> s[j] in uppercase
  {
    if 'A' <= s[i] <= 'Z' {
      var previous := uppercase;
      assert forall c :: c in previous ==> 'A' <= c <= 'Z';
      assert forall j :: 0 <= j < i && 'A' <= s[j] <= 'Z' ==> s[j] in previous;
      uppercase := previous + [s[i]];

      forall c | c in uppercase
        ensures 'A' <= c <= 'Z'
      {
        assert uppercase == previous + [s[i]];
        assert exists k :: 0 <= k < |uppercase| && uppercase[k] == c;
        var k :| 0 <= k < |uppercase| && uppercase[k] == c;
        if k < |previous| {
          assert uppercase[k] == previous[k];
          assert previous[k] == c;
          assert c in previous;
          assert 'A' <= c <= 'Z';
        } else {
          assert |uppercase| == |previous| + 1;
          assert k == |previous|;
          assert k - |previous| == 0;
          assert uppercase[k] == [s[i]][k - |previous|];
          assert [s[i]][0] == s[i];
          assert c == s[i];
          assert 'A' <= c <= 'Z';
        }
      }

      forall j | 0 <= j < i + 1 && 'A' <= s[j] <= 'Z'
        ensures s[j] in uppercase
      {
        assert uppercase == previous + [s[i]];
        if j < i {
          assert s[j] in previous;
          assert s[j] in uppercase;
        } else {
          assert j == i;
          assert s[j] == s[i];
          assert s[j] in [s[i]];
          assert s[j] in uppercase;
        }
      }
    } else {
      forall j | 0 <= j < i + 1 && 'A' <= s[j] <= 'Z'
        ensures s[j] in uppercase
      {
        if j < i {
          assert s[j] in uppercase;
        } else {
          assert j == i;
          assert s[j] == s[i];
          assert 'A' <= s[i] <= 'Z';
          assert false;
        }
      }
    }
    i := i + 1;
  }

  forall c | c in s && 'A' <= c <= 'Z'
    ensures c in uppercase
  {
    assert exists j :: 0 <= j < |s| && s[j] == c;
    var j :| 0 <= j < |s| && s[j] == c;
    assert i == |s|;
    assert 0 <= j < i;
    assert s[j] == c;
    assert 'A' <= s[j] <= 'Z';
    assert s[j] in uppercase;
    assert c in uppercase;
  }
}