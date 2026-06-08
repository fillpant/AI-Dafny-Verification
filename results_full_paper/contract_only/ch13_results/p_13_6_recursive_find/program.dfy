function find(text: string, str: string): bool{
  if |text| < |str| then false
  else if text[0 .. |str|] == str then true
  else find(text[1..], str)
}

method p_13_6_recursive_find(text: string, str: string) returns (found: bool)
	requires 1 <= |str| <= |text|
	ensures found == find(text, str)
{
  if text[0 .. |str|] == str {
    found := true;
  } else if |text| == |str| {
    assert text[0 .. |str|] != str;
    assert |text[1..]| == |text| - 1;
    assert |text[1..]| < |str|;
    found := false;
  } else {
    assert |str| < |text|;
    assert |text[1..]| == |text| - 1;
    assert |str| <= |text[1..]|;
    found := p_13_6_recursive_find(text[1..], str);
  }
}