method p_5_5_repeat(str: string, n: int) returns (repeated_str: string)
	requires n >= 0
	ensures |repeated_str| == n * |str|
	ensures forall i :: 0 <= i < n ==> repeated_str[i * |str| .. (i + 1) * |str| ] == str
{
  if n == 0 {
    repeated_str := "";
    assert |repeated_str| == 0;
    assert 0 * |str| == 0;
  } else {
    var L := |str|;
    var m := n - 1;
    assert 0 <= m;
    assert n == m + 1;

    var prev := p_5_5_repeat(str, m);
    repeated_str := prev + str;

    assert |prev| == m * L;
    assert |repeated_str| == |prev| + L;
    assert m * L + L == (m + 1) * L;
    assert |repeated_str| == (m + 1) * L;
    assert |repeated_str| == n * L;
    assert repeated_str[..|prev|] == prev;
    assert repeated_str[|prev|..|repeated_str|] == str;

    forall i | 0 <= i < n
      ensures 0 <= i * L && i * L <= (i + 1) * L && (i + 1) * L <= |repeated_str| &&
              repeated_str[i * L .. (i + 1) * L] == str
    {
      assert 0 <= L;
      assert 0 <= i;
      assert i + 1 <= n;
      assert 0 <= n - (i + 1);
      assert 0 <= i * L;
      assert (i + 1) * L == i * L + L;
      assert i * L <= (i + 1) * L;
      assert n * L == (i + 1) * L + (n - (i + 1)) * L;
      assert 0 <= (n - (i + 1)) * L;
      assert (i + 1) * L <= n * L;
      assert (i + 1) * L <= |repeated_str|;

      if i < m {
        assert 0 <= i < m;
        assert i + 1 <= m;
        assert 0 <= m - (i + 1);
        assert m * L == (i + 1) * L + (m - (i + 1)) * L;
        assert 0 <= (m - (i + 1)) * L;
        assert (i + 1) * L <= m * L;
        assert (i + 1) * L <= |prev|;
        assert prev[i * L .. (i + 1) * L] == str;
        assert repeated_str[i * L .. (i + 1) * L] == repeated_str[..|prev|][i * L .. (i + 1) * L];
        assert repeated_str[..|prev|][i * L .. (i + 1) * L] == prev[i * L .. (i + 1) * L];
        assert repeated_str[i * L .. (i + 1) * L] == str;
      } else {
        assert i == m;
        assert i * L == m * L;
        assert i * L == |prev|;
        assert i + 1 == m + 1;
        assert (i + 1) * L == (m + 1) * L;
        assert (i + 1) * L == |repeated_str|;
        assert repeated_str[i * L .. (i + 1) * L] == repeated_str[|prev|..|repeated_str|];
        assert repeated_str[i * L .. (i + 1) * L] == str;
      }
    }

    assert L == |str|;
    assert |repeated_str| == n * |str|;
    assert forall i :: 0 <= i < n ==>
      (0 <= i * |str| && i * |str| <= (i + 1) * |str| && (i + 1) * |str| <= |repeated_str| &&
       repeated_str[i * |str| .. (i + 1) * |str|] == str);
  }
}