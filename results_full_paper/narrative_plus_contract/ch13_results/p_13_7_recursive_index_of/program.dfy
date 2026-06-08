function starts_with(text: string, str: string) : (b: bool)
  ensures b == (|str| <= |text| && forall i :: 0 <= i < |str| ==> text[i] == str[i])
{
  if |str| == 0 then true
  else if |text| == 0 then false
  else if text[0] == str[0] then starts_with(text[1..], str[1..])
  else false
}

function find_index(text: string, str: string, index: nat) : (ret : int)
   ensures starts_with(text, str) ==> ret == index 
{
  if |text| < |str| then -1
  else if starts_with(text, str) then index
  else find_index(text[1..], str, index + 1)
}

method p_13_7_recursive_index_of(text: string, str: string) returns (index: int)
	requires 1 <= |str| <= |text|
	ensures index == find_index(text, str, 0)
{
  var pos: nat := 0;
  assert text[0..] == text;

  while pos + |str| <= |text|
    invariant pos <= |text|
    invariant 1 <= |str| <= |text|
    invariant find_index(text, str, 0) == find_index(text[pos..], str, pos)
    decreases |text| - pos
  {
    if text[pos..][..|str|] == str {
      assert |str| <= |text[pos..]|;
      assert forall i :: 0 <= i < |str| ==> text[pos..][i] == str[i];
      assert starts_with(text[pos..], str) == (|str| <= |text[pos..]| && forall i :: 0 <= i < |str| ==> text[pos..][i] == str[i]);
      assert starts_with(text[pos..], str);
      assert find_index(text[pos..], str, pos) == pos;
      index := pos;
      return;
    } else {
      assert !starts_with(text[pos..], str) by {
        if starts_with(text[pos..], str) {
          assert starts_with(text[pos..], str) == (|str| <= |text[pos..]| && forall i :: 0 <= i < |str| ==> text[pos..][i] == str[i]);
          assert forall i :: 0 <= i < |str| ==> text[pos..][i] == str[i];
          assert |text[pos..][..|str|]| == |str|;
          assert forall i :: 0 <= i < |str| ==> text[pos..][..|str|][i] == str[i];
          assert text[pos..][..|str|] == str;
          assert false;
        }
      }
      assert |str| <= |text[pos..]|;
      assert text[pos..][1..] == text[pos + 1..];
      assert find_index(text[pos..], str, pos) == find_index(text[pos..][1..], str, pos + 1);
      assert find_index(text[pos..], str, pos) == find_index(text[pos + 1..], str, pos + 1);
      pos := pos + 1;
    }
  }

  assert !(pos + |str| <= |text|);
  assert |text[pos..]| == |text| - pos;
  assert |text[pos..]| < |str|;
  assert find_index(text[pos..], str, pos) == -1;
  assert find_index(text, str, 0) == -1;
  index := -1;
}