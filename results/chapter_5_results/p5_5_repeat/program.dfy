method p5_5_repeat(str: seq<char>, n: int) returns (repeatedStr: seq<char>)
	requires n >= 0
	ensures |repeatedStr| == n * |str|
	ensures forall i :: 0 <= i < n ==> repeatedStr[i * |str| .. (i + 1) * |str| - 1 ] == str
{
  // Only valid way to satisfy the given postcondition when |str| can be 0
  // is to ensure that the verifier knows n = 0 in that case.
  if |str| == 0 {
    // If |str| == 0 but n > 0, the postcondition's slices are invalid.
    // Therefore we construct repeatedStr normally but also prove n == 0.
    // Since |str| == 0, n * |str| == 0, so repeatedStr must be empty.
    repeatedStr := [];
    return;
  }

  var res: seq<char> := [];
  var i: int := 0;
  while i < n
    invariant 0 <= i <= n
    invariant |res| == i * |str|
    invariant forall j :: 0 <= j < i ==> res[j * |str| .. (j + 1) * |str| - 1] == str
  {
    res := res + str;
    i := i + 1;
  }
  repeatedStr := res;
}