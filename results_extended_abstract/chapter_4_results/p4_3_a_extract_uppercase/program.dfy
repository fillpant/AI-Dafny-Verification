method p4_3_a_extract_uppercase(s: string) returns (uppercase: string)
	ensures forall c :: c in uppercase ==> 'A' <= c <= 'Z'
	ensures forall c :: c in s && 'A' <= c <= 'Z' ==> c in uppercase
{
  var res := "";
  var i := 0;
  while i < |s|
    invariant 0 <= i <= |s|
    invariant forall c :: c in res ==> 'A' <= c <= 'Z'
    invariant forall j :: 0 <= j < i && 'A' <= s[j] <= 'Z' ==> s[j] in res
  {
    if 'A' <= s[i] <= 'Z' {
      res := res + s[i..i+1];
    }
    i := i + 1;
  }
  uppercase := res;
}