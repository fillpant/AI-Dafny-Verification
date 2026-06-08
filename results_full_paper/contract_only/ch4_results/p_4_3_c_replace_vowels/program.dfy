method p_4_3_c_replace_vowels(s: string) returns (result: string)
	ensures |result| == |s|
	ensures forall i :: 0 <= i < |s| ==> (if s[i] in ['a','e','i','o','u','A','E','I','O','U'] then result[i] == '_' else result[i] == s[i])
{
  result := "";
  var i := 0;
  while i < |s|
    invariant 0 <= i <= |s|
    invariant |result| == i
    invariant forall j :: 0 <= j < i ==> (if s[j] in ['a', 'e', 'i', 'o', 'u', 'A', 'E', 'I', 'O', 'U'] then result[j] == '_' else result[j] == s[j])
  {
    var c := if s[i] in ['a', 'e', 'i', 'o', 'u', 'A', 'E', 'I', 'O', 'U'] then '_' else s[i];
    result := result + [c];
    i := i + 1;
  }
}