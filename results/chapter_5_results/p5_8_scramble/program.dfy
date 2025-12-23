method p5_8_word_scramble(word: string) returns (scrambled: string)
	requires 1 <= |word|
	ensures |word| == |scrambled|
	ensures word[0] == scrambled[0]
	ensures word[|word| - 1] == scrambled[|scrambled| - 1]
	ensures |word| >= 4 ==>  exists i, j :: 1 <= i < j <= |word| - 2 && word[i] == scrambled[j] && word[j] == scrambled[i] && forall k:: 0 <= k <= |word| -1 ==> (k!=i && k!=j ==> word[k] == scrambled[k])
{
  if |word| < 4 {
    scrambled := word;
  } else {
    var i := 1;
    var j := 2;
    var c1 := word[i];
    var c2 := word[j];
    var tmp := word[i := c2];
    scrambled := tmp[j := c1];
  }
}