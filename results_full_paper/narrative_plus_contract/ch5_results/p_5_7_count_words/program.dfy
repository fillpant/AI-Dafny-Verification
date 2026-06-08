function remove_leading_spaces(s: string): (result: string)
    ensures |s| > 0 && s[0] == ' ' ==> |result| < |s|
{
    if |s| == 0 then s
    else if s[0] == ' ' then remove_leading_spaces(s[1..])
    else s
}

function remove_word(s: string): (result: string)
    ensures |s| > 0 && s[0] != ' ' ==> |result| < |s|
{
    if |s| == 0 then s
    else if s[0] != ' ' then remove_word(s[1..])
    else s
}

function count_words(s: string): int
    decreases |s|
{
    var s2 := remove_leading_spaces(s);
    if |s2| > 0 then 1 + count_words(remove_word(s2))
    else 0
}

method p_5_7_count_words(str: string) returns (word_count: int)
	ensures word_count == count_words(str)
{
  if |str| == 0 {
    word_count := 0;
    assert remove_leading_spaces(str) == str;
    assert count_words(str) == 0;
  } else if str[0] == ' ' {
    var rest := p_5_7_count_words(str[1..]);
    word_count := rest;
    assert str[1..] == str[1..];
    assert remove_leading_spaces(str) == remove_leading_spaces(str[1..]);
    assert count_words(str) == count_words(str[1..]);
  } else {
    var i := 0;
    while i < |str| && str[i] != ' '
      invariant 0 <= i <= |str|
      invariant remove_word(str) == remove_word(str[i..])
    {
      assert |str[i..]| > 0;
      assert str[i..][0] == str[i];
      assert str[i..][1..] == str[i + 1..];
      assert remove_word(str[i..]) == remove_word(str[i + 1..]);
      i := i + 1;
    }

    assert i > 0;
    if i < |str| {
      assert str[i] == ' ';
      assert |str[i..]| > 0;
      assert str[i..][0] == ' ';
      assert remove_word(str[i..]) == str[i..];
    } else {
      assert i == |str|;
      assert str[i..] == "";
      assert remove_word(str[i..]) == "";
    }
    assert remove_word(str) == str[i..];

    var rest := p_5_7_count_words(str[i..]);
    word_count := 1 + rest;
    assert remove_leading_spaces(str) == str;
    assert count_words(str) == 1 + count_words(remove_word(str));
    assert count_words(str) == 1 + count_words(str[i..]);
  }
}