method p_4_3_c_replace_vowels(s: string) returns (result: string)
	ensures |result| == |s|
	ensures forall i :: 0 <= i < |s| ==> (if s[i] in ['a','e','i','o','u','A','E','I','O','U'] then result[i] == '_' else result[i] == s[i])
{
  result := seq(|s|, i =>
    if 0 <= i < |s| && s[i] in ['a', 'e', 'i', 'o', 'u', 'A', 'E', 'I', 'O', 'U'] then '_' else
    if 0 <= i < |s| then s[i] else '_');
}