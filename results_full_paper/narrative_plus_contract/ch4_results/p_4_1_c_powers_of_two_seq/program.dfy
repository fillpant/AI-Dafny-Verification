function pow(base: int, exp: int): int
  requires  0 <= exp
  decreases exp
{
  if exp == 0 then 1 else base * pow(base, exp - 1)
}

method p_4_1_c_powers_of_two_seq() returns (powers: seq<int>)
	ensures |powers| == 21
	ensures forall i :: 0 <= i < |powers| ==> powers[i] == pow(2, i)
{
  powers := [];
  var i := 0;
  var current := 1;

  while i < 21
    invariant 0 <= i <= 21
    invariant |powers| == i
    invariant current == pow(2, i)
    invariant forall j :: 0 <= j < i ==> powers[j] == pow(2, j)
    decreases 21 - i
  {
    var nextI := i + 1;
    var oldPowers := powers;

    powers := oldPowers + [current];
    assert |powers| == nextI;
    assert powers[i] == current;

    forall j | 0 <= j < nextI
      ensures powers[j] == pow(2, j)
    {
      if j < i {
        assert powers[j] == oldPowers[j];
      } else {
        assert j == i;
        assert powers[j] == current;
      }
    }

    current := current * 2;
    assert current == pow(2, i) * 2;
    assert current == 2 * pow(2, i);
    assert 0 < nextI;
    assert nextI - 1 == i;
    assert pow(2, nextI) == 2 * pow(2, nextI - 1);
    assert pow(2, nextI) == 2 * pow(2, i);
    assert current == pow(2, nextI);

    i := nextI;
  }

  assert i == 21;
  assert |powers| == 21;
  forall j | 0 <= j < |powers|
    ensures powers[j] == pow(2, j)
  {
    assert j < i;
  }
}