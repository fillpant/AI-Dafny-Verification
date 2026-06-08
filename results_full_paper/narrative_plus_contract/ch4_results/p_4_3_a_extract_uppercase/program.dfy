method p_4_3_a_extract_uppercase(s: string) returns (uppercase: string)
	ensures forall c :: c in uppercase ==> 'A' <= c <= 'Z'
	ensures forall c :: c in s && 'A' <= c <= 'Z' ==> c in uppercase
{
  uppercase := "";
  var i := 0;
  while i < |s|
    invariant 0 <= i <= |s|
    invariant forall c :: c in uppercase ==> 'A' <= c && c <= 'Z'
    invariant forall c :: c in s[..i] && 'A' <= c && c <= 'Z' ==> c in uppercase
    decreases |s| - i
  {
    var ch := s[i];
    assert s[..i + 1] == s[..i] + [ch];

    if 'A' <= ch && ch <= 'Z' {
      var prev := uppercase;
      assert forall c :: c in prev ==> 'A' <= c && c <= 'Z';
      assert forall c :: c in s[..i] && 'A' <= c && c <= 'Z' ==> c in prev;

      uppercase := prev + [ch];

      forall c | c in uppercase
        ensures 'A' <= c && c <= 'Z'
      {
        if c in prev {
          assert 'A' <= c && c <= 'Z';
        } else {
          assert c in [ch];
          assert c == ch;
        }
      }

      forall c | c in s[..i + 1] && 'A' <= c && c <= 'Z'
        ensures c in uppercase
      {
        if c in s[..i] {
          assert c in prev;
          assert c in uppercase;
        } else {
          assert c in [ch];
          assert c == ch;
          assert ch in uppercase;
        }
      }
    } else {
      assert !('A' <= ch && ch <= 'Z');

      forall c | c in s[..i + 1] && 'A' <= c && c <= 'Z'
        ensures c in uppercase
      {
        if c in s[..i] {
          assert c in uppercase;
        } else {
          assert c in [ch];
          assert c == ch;
          assert 'A' <= ch && ch <= 'Z';
          assert false;
        }
      }
    }

    i := i + 1;
  }

  assert i == |s|;
  assert s[..i] == s;

  forall c | c in s && 'A' <= c && c <= 'Z'
    ensures c in uppercase
  {
    assert c in s[..i];
  }
}