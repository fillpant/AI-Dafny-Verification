method p5_6_countVowels(str: seq<char>) returns (vowelCount: int)
	ensures vowelCount >= 0
	ensures vowelCount <= |str|
	ensures (forall c :: c in str ==> (c == 'a' || c == 'e' || c == 'i' || c == 'o' || c == 'u' || c == 'A' || c == 'E' || c == 'I' || c == 'O' || c == 'U')) ==> vowelCount == |str|
	ensures (forall c :: c in str ==> !(c == 'a' || c == 'e' || c == 'i' || c == 'o' || c == 'u' || c == 'A' || c == 'E' || c == 'I' || c == 'O' || c == 'U')) ==> vowelCount == 0
{
  vowelCount := 0;
  var i := 0;
  while i < |str|
    invariant 0 <= i <= |str|
    invariant 0 <= vowelCount <= i
    invariant vowelCount == (|{ j:int | 0 <= j < i && (str[j] == 'a' || str[j] == 'e' || str[j] == 'i' || str[j] == 'o' || str[j] == 'u' || str[j] == 'A' || str[j] == 'E' || str[j] == 'I' || str[j] == 'O' || str[j] == 'U') }|)
  {
    if str[i] == 'a' || str[i] == 'e' || str[i] == 'i' || str[i] == 'o' || str[i] == 'u' ||
       str[i] == 'A' || str[i] == 'E' || str[i] == 'I' || str[i] == 'O' || str[i] == 'U'
    {
      vowelCount := vowelCount + 1;
    }
    i := i + 1;
  }
}