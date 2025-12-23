function count_space(str: seq<char>) : int
{
  if |str| == 0 then 0
  else if str[0] == ' ' then 1 + count_space(str[1..])
  else count_space(str[1..])
}

method p5_7_countWords(str: seq<char>) returns (wordCount: int)
	ensures wordCount >= 0
	ensures if |str| == 0 then wordCount == 0 else wordCount >= 1
	ensures wordCount == count_space(str) + 1
{
  // First loop: compute s = number of spaces (concrete state)
  var s := 0;
  var i := 0;
  while i < |str|
    invariant 0 <= i <= |str|
    invariant 0 <= s <= i
    decreases |str| - i
  {
    if str[i] == ' ' {
      s := s + 1;
    }
    i := i + 1;
  }

  // Second loop (ghost): prove s == count_space(str)
  ghost var gs := 0;
  ghost var j := 0;
  while j < |str|
    invariant 0 <= j <= |str|
    invariant gs == count_space(str[..j])
    decreases |str| - j
  {
    if str[j] == ' ' {
      gs := gs + 1;
    }
    j := j + 1;
  }

  // Establish equivalence for the postcondition
  assert s == gs;

  // Now use s only (non‑ghost)
  if |str| == 0 {
    wordCount := 0;
  } else {
    wordCount := s + 1;
  }
}