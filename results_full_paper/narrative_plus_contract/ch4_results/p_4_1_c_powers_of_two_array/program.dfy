function pow(base: int, exp: int): int
  requires  0 <= exp
  decreases exp
{
  if exp == 0 then 1 else base * pow(base, exp - 1)
}

method p_4_1_c_powers_of_two_array() returns (powers: array<int>)
	ensures powers.Length == 21
	ensures forall i :: 0 <= i < powers.Length ==> powers[i] == pow(2, i)
{
  powers := new int[21];
  var i := 0;
  var p := 1;

  while i < 21
    invariant powers.Length == 21
    invariant 0 <= i <= 21
    invariant p == pow(2, i)
    invariant forall j :: 0 <= j < i ==> powers[j] == pow(2, j)
    decreases 21 - i
  {
    var oldI := i;
    var oldP := p;
    assert oldP == pow(2, oldI);

    powers[i] := p;
    assert powers[oldI] == pow(2, oldI);

    p := 2 * p;
    i := i + 1;

    assert i == oldI + 1;
    assert i > 0;
    assert i - 1 == oldI;
    assert pow(2, i) == 2 * pow(2, i - 1);
    assert p == 2 * oldP;
    assert p == pow(2, i);

    forall j | 0 <= j < i
      ensures powers[j] == pow(2, j)
    {
      if j == oldI {
        assert powers[j] == pow(2, j);
      } else {
        assert j < oldI + 1;
        assert j != oldI;
        assert j < oldI;
        assert powers[j] == pow(2, j);
      }
    }
  }
}