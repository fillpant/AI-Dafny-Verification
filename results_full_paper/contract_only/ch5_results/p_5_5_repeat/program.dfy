method p_5_5_repeat(str: string, n: int) returns (repeated_str: string)
	requires n >= 0
	ensures |repeated_str| == n * |str|
	ensures forall i :: 0 <= i < n ==> repeated_str[i * |str| .. (i + 1) * |str| ] == str
{
  repeated_str := "";
  var k := 0;
  while k < n
    invariant 0 <= k <= n
    invariant |repeated_str| == k * |str|
    invariant forall i :: 0 <= i < k ==> 0 <= i * |str| && i * |str| <= (i + 1) * |str| && (i + 1) * |str| <= |repeated_str| && repeated_str[i * |str| .. (i + 1) * |str|] == str
  {
    var prev := repeated_str;

    assert forall i :: 0 <= i < k ==> 0 <= i * |str| && i * |str| <= (i + 1) * |str| && (i + 1) * |str| <= |prev| && prev[i * |str| .. (i + 1) * |str|] == str by {
      forall i | 0 <= i < k
        ensures 0 <= i * |str| && i * |str| <= (i + 1) * |str| && (i + 1) * |str| <= |prev| && prev[i * |str| .. (i + 1) * |str|] == str
      {
        var a := i * |str|;
        var b := (i + 1) * |str|;
        assert prev == repeated_str;
        assert 0 <= a && a <= b && b <= |repeated_str| && repeated_str[a..b] == str;
        assert |prev| == |repeated_str|;
        assert b <= |prev|;
        assert prev[a..b] == repeated_str[a..b];
      }
    }

    repeated_str := prev + str;
    assert repeated_str == prev + str;
    assert |repeated_str| == |prev| + |str|;
    assert |prev| == k * |str|;
    assert |repeated_str| == (k + 1) * |str|;
    assert repeated_str[..|prev|] == prev;
    assert repeated_str[|prev|..] == str;

    assert forall i :: 0 <= i < k + 1 ==> 0 <= i * |str| && i * |str| <= (i + 1) * |str| && (i + 1) * |str| <= |repeated_str| && repeated_str[i * |str| .. (i + 1) * |str|] == str by {
      forall i | 0 <= i < k + 1
        ensures 0 <= i * |str| && i * |str| <= (i + 1) * |str| && (i + 1) * |str| <= |repeated_str| && repeated_str[i * |str| .. (i + 1) * |str|] == str
      {
        var a := i * |str|;
        var b := (i + 1) * |str|;
        if i < k {
          assert 0 <= a && a <= b && b <= |prev| && prev[a..b] == str;
          assert |str| >= 0;
          assert |prev| <= |repeated_str|;
          assert b <= |repeated_str|;
          assert repeated_str[..|prev|] == prev;
          assert repeated_str[a..b] == (repeated_str[..|prev|])[a..b];
          assert (repeated_str[..|prev|])[a..b] == prev[a..b];
          assert repeated_str[a..b] == str;
        } else {
          assert i == k;
          assert a == k * |str|;
          assert a == |prev|;
          assert b == (k + 1) * |str|;
          assert b == |prev| + |str|;
          assert b == |repeated_str|;
          assert 0 <= a;
          assert a <= b;
          assert repeated_str[a..b] == repeated_str[|prev|..|repeated_str|];
          assert repeated_str[|prev|..|repeated_str|] == repeated_str[|prev|..];
          assert repeated_str[a..b] == str;
        }
      }
    }

    k := k + 1;
  }
  assert k == n;
}