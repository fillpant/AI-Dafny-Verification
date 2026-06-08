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
    found := false;
  } else {
    found := p_13_6_recursive_find(text[1..], str);
  }
}