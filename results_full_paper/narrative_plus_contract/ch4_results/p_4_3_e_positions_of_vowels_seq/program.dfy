method p_4_3_e_positions_of_vowels_seq(s: string) returns (positions: seq<int>)
	ensures forall p :: p in positions ==> 0 <= p < |s| && s[p] in ['a','e','i','o','u','A','E','I','O','U']
	ensures forall i :: 0 <= i < |s| && s[i] in ['a','e','i','o','u','A','E','I','O','U'] ==> i in positions
{
  positions := [];
  var i := 0;
  while i < |s|
    invariant 0 <= i <= |s|
    invariant forall p :: p in positions ==> 0 <= p < i && s[p] in ['a','e','i','o','u','A','E','I','O','U']
    invariant forall j :: 0 <= j < i && s[j] in ['a','e','i','o','u','A','E','I','O','U'] ==> j in positions
  {
    if s[i] in ['a','e','i','o','u','A','E','I','O','U'] {
      positions := positions + [i];
    }
    i := i + 1;
  }
}