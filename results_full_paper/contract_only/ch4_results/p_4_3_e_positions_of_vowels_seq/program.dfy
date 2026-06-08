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
    var next := i + 1;
    if s[i] in ['a','e','i','o','u','A','E','I','O','U'] {
      var previous := positions;
      assert forall p :: p in previous ==> 0 <= p < i && s[p] in ['a','e','i','o','u','A','E','I','O','U'];
      assert forall j :: 0 <= j < i && s[j] in ['a','e','i','o','u','A','E','I','O','U'] ==> j in previous;

      positions := previous + [i];

      assert forall p :: p in positions ==> p in previous || p == i;
      assert forall p :: p in previous ==> p in positions;
      assert i in positions;

      assert forall p :: p in positions ==> 0 <= p < next && s[p] in ['a','e','i','o','u','A','E','I','O','U'] by {
        forall p | p in positions
          ensures 0 <= p < next && s[p] in ['a','e','i','o','u','A','E','I','O','U']
        {
          if p == i {
            assert 0 <= i < next;
            assert s[p] == s[i];
          } else {
            assert p in previous;
            assert 0 <= p < i && s[p] in ['a','e','i','o','u','A','E','I','O','U'];
            assert p < next;
          }
        }
      }

      assert forall j :: 0 <= j < next && s[j] in ['a','e','i','o','u','A','E','I','O','U'] ==> j in positions by {
        forall j | 0 <= j < next && s[j] in ['a','e','i','o','u','A','E','I','O','U']
          ensures j in positions
        {
          if j == i {
            assert i in positions;
          } else {
            assert j < i;
            assert j in previous;
            assert j in positions;
          }
        }
      }
    } else {
      assert forall p :: p in positions ==> 0 <= p < next && s[p] in ['a','e','i','o','u','A','E','I','O','U'] by {
        forall p | p in positions
          ensures 0 <= p < next && s[p] in ['a','e','i','o','u','A','E','I','O','U']
        {
          assert 0 <= p < i && s[p] in ['a','e','i','o','u','A','E','I','O','U'];
          assert p < next;
        }
      }

      assert forall j :: 0 <= j < next && s[j] in ['a','e','i','o','u','A','E','I','O','U'] ==> j in positions by {
        forall j | 0 <= j < next && s[j] in ['a','e','i','o','u','A','E','I','O','U']
          ensures j in positions
        {
          if j == i {
            assert s[j] == s[i];
            assert s[i] in ['a','e','i','o','u','A','E','I','O','U'];
            assert !(s[i] in ['a','e','i','o','u','A','E','I','O','U']);
            assert false;
          } else {
            assert j < i;
            assert j in positions;
          }
        }
      }
    }
    i := next;
  }
}