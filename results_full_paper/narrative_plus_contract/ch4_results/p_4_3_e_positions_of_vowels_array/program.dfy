method p_4_3_e_positions_of_vowels_array(s: string) returns (positions: array<int>)
	ensures forall p :: p in positions[..] ==> 0 <= p < |s| && s[p] in ['a','e','i','o','u','A','E','I','O','U']
	ensures forall i :: 0 <= i < |s| && s[i] in ['a','e','i','o','u','A','E','I','O','U'] ==> i in positions[..]
{
  var vowels := ['a', 'e', 'i', 'o', 'u', 'A', 'E', 'I', 'O', 'U'];
  var ps: seq<int> := [];
  var i := 0;

  while i < |s|
    invariant 0 <= i <= |s|
    invariant forall p :: p in ps ==> 0 <= p < i && s[p] in vowels
    invariant forall j :: 0 <= j < i && s[j] in vowels ==> j in ps
  {
    if s[i] in vowels {
      var newPs := ps + [i];

      forall p | p in newPs
        ensures 0 <= p < i + 1 && s[p] in vowels
      {
        if p in ps {
          assert 0 <= p < i && s[p] in vowels;
        } else {
          assert p in [i];
          assert p == i;
        }
      }

      forall j | 0 <= j < i + 1 && s[j] in vowels
        ensures j in newPs
      {
        if j < i {
          assert j in ps;
          assert j in newPs;
        } else {
          assert j == i;
          assert j in [i];
          assert j in newPs;
        }
      }

      ps := newPs;
    } else {
      forall p | p in ps
        ensures 0 <= p < i + 1 && s[p] in vowels
      {
        assert 0 <= p < i && s[p] in vowels;
      }

      forall j | 0 <= j < i + 1 && s[j] in vowels
        ensures j in ps
      {
        if j < i {
          assert j in ps;
        } else {
          assert j == i;
          assert s[j] == s[i];
          assert false;
        }
      }
    }

    i := i + 1;
  }

  assert i == |s|;
  positions := new int[|ps|](k => if 0 <= k && k < |ps| then ps[k] else 0);

  assert positions.Length == |ps|;
  forall k | 0 <= k < |ps|
    ensures positions[..][k] == ps[k]
  {
    assert positions[k] == ps[k];
    assert positions[..][k] == positions[k];
  }
  assert |positions[..]| == |ps|;
  assert positions[..] == ps;

  assert vowels == ['a', 'e', 'i', 'o', 'u', 'A', 'E', 'I', 'O', 'U'];
  assert forall p :: p in positions[..] ==> 0 <= p < |s| && s[p] in ['a', 'e', 'i', 'o', 'u', 'A', 'E', 'I', 'O', 'U'];
  assert forall j :: 0 <= j < |s| && s[j] in ['a', 'e', 'i', 'o', 'u', 'A', 'E', 'I', 'O', 'U'] ==> j in positions[..];
}