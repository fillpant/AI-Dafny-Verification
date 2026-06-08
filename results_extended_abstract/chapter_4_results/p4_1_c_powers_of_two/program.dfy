function pow(base: int, exp: int): int
  requires  0 <= exp
  decreases exp
{
  if exp == 0 then 1 else base * pow(base, exp - 1)
}

method p4_1_c_powers_of_two() returns (powers: seq<int>)
	ensures |powers| == 21
	ensures forall i :: 0 <= i < |powers| ==> powers[i] == pow(2, i)
{
  var res: seq<int> := [];
  var cur: int := 1;
  var i: int := 0;
  while i <= 20
    invariant 0 <= i <= 21
    invariant |res| == i
    invariant cur == pow(2, i)
    invariant forall k :: 0 <= k < i ==> res[k] == pow(2, k)
  {
    res := res + [cur];
    cur := cur * 2;
    i := i + 1;
  }
  powers := res;
}