function count_vowels(s: string): int {
  if s == "" then 0
  else if s[0] in ['a','e','i','o','u','A','E','I','O','U'] then count_vowels(s[1..]) + 1
  else count_vowels(s[1..])
}

method p_4_3_d_count_vowels(s: string) returns (count: int)
	ensures count == count_vowels(s) 
{
  if s == "" {
    count := 0;
  } else {
    var rest := p_4_3_d_count_vowels(s[1..]);
    if s[0] in ['a', 'e', 'i', 'o', 'u', 'A', 'E', 'I', 'O', 'U'] {
      count := rest + 1;
    } else {
      count := rest;
    }
  }
}