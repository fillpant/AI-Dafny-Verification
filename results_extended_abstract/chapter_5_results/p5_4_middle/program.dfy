method p5_4_middle(str: seq<char>) returns (middleStr: seq<char>)
	requires 0 < |str|
	ensures if |str| % 2 == 1 then |middleStr| == 1 else |middleStr| == 2
	ensures if |str| % 2 == 1 then middleStr[0] == str[|str| / 2] else middleStr == str[|str| / 2 - 1 .. |str| / 2]
{
  var n := |str|;
  if n % 2 == 1 {
    middleStr := [str[n/2]];
  } else {
    // To satisfy both postconditions, the slice must have length 2
    middleStr := str[n/2 - 1 .. n/2 + 1];
  }
}