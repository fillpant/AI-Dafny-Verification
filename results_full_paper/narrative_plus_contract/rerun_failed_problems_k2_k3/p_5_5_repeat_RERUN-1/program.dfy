method p_5_5_repeat(str: string, n: int) returns (repeated_str: string)
	requires n >= 0
	ensures |repeated_str| == n * |str|
	ensures forall i :: 0 <= i < n ==> repeated_str[i * |str| .. (i + 1) * |str| ] == str
{
  repeated_str := "";
  var k := 0;
  var m := |str|;

  while k < n
    invariant 0 <= k <= n
    invariant m == |str|
    invariant 0 <= m
    invariant |repeated_str| == k * m
    invariant |repeated_str| == k * |str|
    invariant forall i:int :: 0 <= i < k ==> repeated_str[i * |str| .. (i + 1) * |str|] == str
    decreases n - k
  {
    var old_repeated_str := repeated_str;
    assert |old_repeated_str| == k * m;
    assert forall i:int :: 0 <= i < k ==> old_repeated_str[i * |str| .. (i + 1) * |str|] == str;

    repeated_str := old_repeated_str + str;

    assert |repeated_str| == |old_repeated_str| + |str|;
    assert |old_repeated_str| == k * m;
    assert |str| == m;
    assert |repeated_str| == k * m + m;
    assert k * m + m == (k + 1) * m;
    assert |repeated_str| == (k + 1) * m;
    assert |repeated_str| == (k + 1) * |str|;

    forall i:int | 0 <= i < k + 1
      ensures repeated_str[i * |str| .. (i + 1) * |str|] == str
    {
      var a := i * m;
      var b := (i + 1) * m;
      assert a == i * |str|;
      assert b == (i + 1) * |str|;
      assert 0 <= i;
      assert 0 <= m;
      assert 0 <= a;
      assert b == a + m;
      assert a <= b;

      if i < k {
        assert i + 1 <= k;
        var d := k - (i + 1);
        assert 0 <= d;
        assert k == i + 1 + d;
        assert k * m == (i + 1 + d) * m;
        assert (i + 1 + d) * m == (i + 1) * m + d * m;
        assert 0 <= d * m;
        assert (i + 1) * m <= (i + 1) * m + d * m;
        assert (i + 1) * m <= k * m;
        assert b <= k * m;
        assert b <= |old_repeated_str|;
        assert b <= |repeated_str|;

        assert old_repeated_str[a .. b] == str;

        forall j:int | 0 <= j < b - a
          ensures repeated_str[a .. b][j] == old_repeated_str[a .. b][j]
        {
          assert 0 <= a + j;
          assert a + j < b;
          assert a + j < |old_repeated_str|;
          assert repeated_str == old_repeated_str + str;
          assert repeated_str[a + j] == old_repeated_str[a + j];
          assert repeated_str[a .. b][j] == repeated_str[a + j];
          assert old_repeated_str[a .. b][j] == old_repeated_str[a + j];
        }
        assert |repeated_str[a .. b]| == |old_repeated_str[a .. b]|;
        assert repeated_str[a .. b] == old_repeated_str[a .. b];
        assert repeated_str[a .. b] == str;
      } else {
        assert i == k;
        assert a == k * m;
        assert a == |old_repeated_str|;
        assert b == (k + 1) * m;
        assert b == k * m + m;
        assert b == |old_repeated_str| + |str|;
        assert b == |repeated_str|;
        assert b - a == |str|;

        forall j:int | 0 <= j < |str|
          ensures repeated_str[a .. b][j] == str[j]
        {
          assert 0 <= j < b - a;
          assert repeated_str[a .. b][j] == repeated_str[a + j];
          assert a == |old_repeated_str|;
          assert a + j == |old_repeated_str| + j;
          assert repeated_str == old_repeated_str + str;
          assert repeated_str[a + j] == str[j];
        }
        assert |repeated_str[a .. b]| == |str|;
        assert repeated_str[a .. b] == str;
      }

      assert repeated_str[a .. b] == str;
      assert repeated_str[i * |str| .. (i + 1) * |str|] == str;
    }

    k := k + 1;
  }

  assert k == n;
}