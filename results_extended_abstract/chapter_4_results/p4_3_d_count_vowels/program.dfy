method p4_3_d_count_vowels(s: string) returns (count: int)
	ensures count >= 0
	ensures forall c :: c in s && c in ['a','e','i','o','u','A','E','I','O','U'] ==> count >= 1
	ensures (forall c :: c in s ==> c !in ['a','e','i','o','u','A','E','I','O','U']) ==> count == 0
{
  count := 0;
  ghost var hasVowel := false;
  var i := 0;
  while i < |s|
    invariant 0 <= i <= |s|
    invariant count >= 0
    invariant hasVowel == (exists j :: 0 <= j < i && ((s[j] == 'a' || s[j] == 'e' || s[j] == 'i' || s[j] == 'o' || s[j] == 'u' || s[j] == 'A' || s[j] == 'E' || s[j] == 'I' || s[j] == 'O' || s[j] == 'U')))
    invariant hasVowel ==> count >= 1
    invariant !hasVowel ==> count == 0
  {
    var c := s[i];
    var isVowel := c == 'a' || c == 'e' || c == 'i' || c == 'o' || c == 'u' ||
                   c == 'A' || c == 'E' || c == 'I' || c == 'O' || c == 'U';
    if isVowel {
      count := count + 1;
      hasVowel := true;
    }
    i := i + 1;
  }
}