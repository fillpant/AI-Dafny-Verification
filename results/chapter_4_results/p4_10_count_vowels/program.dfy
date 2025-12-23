method p4_10_count_vowels(s: string) returns (count: int)
	ensures 0 <= count
	ensures forall c :: c in s ==> c in ['a','e','i','o','u','A','E','I','O','U'] ==> count >= 1
	ensures (forall c :: c in s ==> c !in ['a','e','i','o','u','A','E','I','O','U']) ==> count == 0
{
  count := 0;
  ghost var vowelIdxs : set<int> := {};
  var i := 0;
  while i < |s|
    invariant 0 <= i <= |s|
    invariant 0 <= count
    invariant vowelIdxs == set j:int | 0 <= j < i && (s[j] == 'a' || s[j] == 'e' || s[j] == 'i' || s[j] == 'o' || s[j] == 'u' || s[j] == 'A' || s[j] == 'E' || s[j] == 'I' || s[j] == 'O' || s[j] == 'U')
    invariant count == |vowelIdxs|
  {
    if s[i] == 'a' || s[i] == 'e' || s[i] == 'i' || s[i] == 'o' || s[i] == 'u' ||
       s[i] == 'A' || s[i] == 'E' || s[i] == 'I' || s[i] == 'O' || s[i] == 'U' {
      vowelIdxs := vowelIdxs + {i};
      count := count + 1;
    }
    i := i + 1;
  }
}