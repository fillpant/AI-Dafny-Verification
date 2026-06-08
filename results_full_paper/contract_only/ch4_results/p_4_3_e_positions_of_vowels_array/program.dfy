method p_4_3_e_positions_of_vowels_array(s: string) returns (positions: array<int>)
	ensures forall p :: p in positions[..] ==> 0 <= p < |s| && s[p] in ['a','e','i','o','u','A','E','I','O','U']
	ensures forall i :: 0 <= i < |s| && s[i] in ['a','e','i','o','u','A','E','I','O','U'] ==> i in positions[..]
{
  var acc: seq<int> := [];
  var i := 0;
  while i < |s|
    invariant 0 <= i <= |s|
    invariant forall p :: p in acc ==> 0 <= p < i && s[p] in ['a','e','i','o','u','A','E','I','O','U']
    invariant forall j :: 0 <= j < i && s[j] in ['a','e','i','o','u','A','E','I','O','U'] ==> j in acc
  {
    if s[i] in ['a','e','i','o','u','A','E','I','O','U'] {
      acc := acc + [i];
    }
    assert forall p :: p in acc ==> 0 <= p < i + 1 && s[p] in ['a','e','i','o','u','A','E','I','O','U'];
    assert forall j :: 0 <= j < i + 1 && s[j] in ['a','e','i','o','u','A','E','I','O','U'] ==> j in acc;
    i := i + 1;
  }

  positions := new int[|acc|](j => if 0 <= j < |acc| then acc[j] else 0);
  assert positions.Length == |acc|;
  assert forall j :: 0 <= j < |acc| ==> positions[j] == acc[j];
  assert forall j :: 0 <= j < |positions[..]| ==> positions[..][j] == acc[j];
  assert positions[..] == acc;
}