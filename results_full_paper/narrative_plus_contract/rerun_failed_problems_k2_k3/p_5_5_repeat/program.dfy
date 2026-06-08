method p_5_5_repeat(str: string, n: int) returns (repeated_str: string)
	requires n >= 0
	ensures |repeated_str| == n * |str|
	ensures forall i :: 0 <= i < n ==> repeated_str[i * |str| .. (i + 1) * |str| ] == str
{
  var L := |str|;
  repeated_str := "";
  var k := 0;

  while k < n
    invariant L == |str|
    invariant 0 <= L
    invariant 0 <= k <= n
    invariant |repeated_str| == k * L
    invariant forall j {:trigger repeated_str[j * L .. (j + 1) * L]} :: 0 <= j < k ==> (0 <= j * L <= (j + 1) * L <= |repeated_str| && repeated_str[j * L .. (j + 1) * L] == str)
  {
    var old_repeated := repeated_str;
    assert |old_repeated| == k * L;
    assert forall j {:trigger old_repeated[j * L .. (j + 1) * L]} :: 0 <= j < k ==> (0 <= j * L <= (j + 1) * L <= |old_repeated| && old_repeated[j * L .. (j + 1) * L] == str);

    repeated_str := old_repeated + str;
    assert repeated_str == old_repeated + str;
    assert |repeated_str| == |old_repeated| + L;
    assert (k + 1) * L == k * L + L;
    assert |repeated_str| == (k + 1) * L;

    forall j: int {:trigger repeated_str[j * L .. (j + 1) * L]} | 0 <= j < k + 1
      ensures 0 <= j * L <= (j + 1) * L <= |repeated_str| && repeated_str[j * L .. (j + 1) * L] == str
    {
      assert j <= k;
      assert 0 <= j * L;
      assert (j + 1) * L == j * L + L;
      assert j * L <= (j + 1) * L;
      assert 0 <= k - j;
      assert k + 1 == (j + 1) + (k - j);
      assert (k + 1) * L == (j + 1) * L + (k - j) * L;
      assert 0 <= (k - j) * L;
      assert (j + 1) * L <= (k + 1) * L;
      assert 0 <= j * L <= (j + 1) * L <= |repeated_str|;

      if j < k {
        var lo := j * L;
        var hi := (j + 1) * L;
        assert j + 1 <= k;
        assert 0 <= k - (j + 1);
        assert k == (j + 1) + (k - (j + 1));
        assert k * L == (j + 1) * L + (k - (j + 1)) * L;
        assert 0 <= (k - (j + 1)) * L;
        assert hi <= k * L;
        assert hi <= |old_repeated|;
        assert old_repeated[lo .. hi] == str;
        assert repeated_str[.. |old_repeated|] == old_repeated;
        assert repeated_str[lo .. hi] == repeated_str[.. |old_repeated|][lo .. hi];
        assert repeated_str[.. |old_repeated|][lo .. hi] == old_repeated[lo .. hi];
        assert repeated_str[lo .. hi] == str;
      } else {
        assert j == k;
        var lo := j * L;
        var hi := (j + 1) * L;
        assert lo == |old_repeated|;
        assert hi == |old_repeated| + L;
        assert hi == |repeated_str|;
        assert repeated_str[|old_repeated| .. |repeated_str|] == str;
        assert repeated_str[lo .. hi] == str;
      }
    }

    k := k + 1;
  }

  assert k == n;
  assert L == |str|;
  assert |repeated_str| == n * |str|;

  forall j: int {:trigger repeated_str[j * |str| .. (j + 1) * |str|]} | 0 <= j < n
    ensures repeated_str[j * |str| .. (j + 1) * |str|] == str
  {
    assert 0 <= j * L;
    assert (j + 1) * L == j * L + L;
    assert j * L <= (j + 1) * L;
    assert j <= n - 1;
    assert j + 1 <= n;
    assert 0 <= n - (j + 1);
    assert n == (j + 1) + (n - (j + 1));
    assert n * L == (j + 1) * L + (n - (j + 1)) * L;
    assert 0 <= (n - (j + 1)) * L;
    assert (j + 1) * L <= n * L;
    assert 0 <= j * L <= (j + 1) * L <= |repeated_str|;
    assert repeated_str[j * L .. (j + 1) * L] == str;
    assert j * |str| == j * L;
    assert (j + 1) * |str| == (j + 1) * L;
    assert repeated_str[j * |str| .. (j + 1) * |str|] == str;
  }
}