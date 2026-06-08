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
  powers[0] := 1;
  assert powers[0] == pow(2, 0);

  var i := 1;
  while i < powers.Length
    invariant powers.Length == 21
    invariant 1 <= i <= powers.Length
    invariant forall j :: 0 <= j < i ==> powers[j] == pow(2, j)
  {
    powers[i] := 2 * powers[i - 1];
    assert 0 <= i - 1;
    assert powers[i - 1] == pow(2, i - 1);
    assert i != 0;
    assert pow(2, i) == 2 * pow(2, i - 1);
    assert powers[i] == pow(2, i);

    assert forall j :: 0 <= j < i + 1 ==> powers[j] == pow(2, j) by {
      forall j | 0 <= j < i + 1
        ensures powers[j] == pow(2, j)
      {
        if j < i {
          assert powers[j] == pow(2, j);
        } else {
          assert j == i;
          assert powers[j] == pow(2, j);
        }
      }
    }
    i := i + 1;
  }
}