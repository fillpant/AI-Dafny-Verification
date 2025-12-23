method p4_3_c_replace_vowels(s: string) returns (result: string)
	ensures |result| == |s|
	ensures forall i :: 0 <= i < |s| ==> (if s[i] in ['a','e','i','o','u','A','E','I','O','U'] then result[i] == '_' else result[i] == s[i])
{
  var arr := new char[|s|];
  var i := 0;
  while i < |s|
    invariant 0 <= i <= |s|
    invariant forall j :: 0 <= j < i ==> (if s[j] == 'a' || s[j] == 'e' || s[j] == 'i' || s[j] == 'o' || s[j] == 'u' || s[j] == 'A' || s[j] == 'E' || s[j] == 'I' || s[j] == 'O' || s[j] == 'U' then arr[j] == '_' else arr[j] == s[j])
  {
    var c := s[i];
    if c == 'a' || c == 'e' || c == 'i' || c == 'o' || c == 'u' ||
       c == 'A' || c == 'E' || c == 'I' || c == 'O' || c == 'U'
    {
      arr[i] := '_';
    } else {
      arr[i] := c;
    }
    i := i + 1;
  }
  result := arr[..];
}