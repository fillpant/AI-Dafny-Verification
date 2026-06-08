method p_14_4_merge_sort_lexicographic_array(inputs: array<string>) returns (sorted: array<string>)
	ensures forall i, j :: 0 <= i < j < sorted.Length ==> sorted[i] <= sorted[j]
	ensures multiset(inputs[..]) == multiset(sorted[..])
{
  var rest := inputs[..];
  var res: seq<string> := [];

  while |rest| > 0
    invariant multiset(res) + multiset(rest) == multiset(inputs[..])
    invariant forall i: int, j: int :: 0 <= i < j < |res| ==> res[i] <= res[j]
    decreases |rest|
  {
    var oldRest := rest;
    assert multiset(res) + multiset(oldRest) == multiset(inputs[..]);

    var x := oldRest[0];
    rest := oldRest[1..];
    assert oldRest == [x] + rest;
    assert multiset(oldRest) == multiset([x]) + multiset(rest);

    var k := 0;
    while k < |res| && res[k] <= x
      invariant 0 <= k <= |res|
      invariant forall t: int :: 0 <= t < k ==> res[t] <= x
      invariant forall i: int, j: int :: 0 <= i < j < |res| ==> res[i] <= res[j]
      decreases |res| - k
    {
      assert res[k] <= x;
      k := k + 1;
    }

    if k < |res| {
      assert !(res[k] <= x);
      var y := res[k];
      var n := if |x| <= |y| then |x| else |y|;
      assert n <= |x| && n <= |y|;
      var p := 0;
      while p < n && x[p] == y[p]
        invariant 0 <= p <= n
        invariant n <= |x| && n <= |y|
        invariant forall q: int :: 0 <= q < p ==> x[q] == y[q]
        decreases n - p
      {
        p := p + 1;
      }
      if p == n {
        if |x| <= |y| {
          assert n == |x|;
          assert forall q: int :: 0 <= q < |x| ==> x[q] == y[q];
          assert x <= y;
        } else {
          assert n == |y|;
          assert forall q: int :: 0 <= q < |y| ==> y[q] == x[q];
          assert y <= x;
        }
      } else {
        assert p < n;
        assert p < |x| && p < |y|;
        assert x[p] != y[p];
        if x[p] < y[p] {
          assert x <= y;
        } else {
          assert y[p] < x[p];
          assert y <= x;
        }
      }
      assert x <= y || y <= x;
      assert y == res[k];
      assert x <= res[k] || res[k] <= x;
      assert x <= res[k];
    }
    assert k < |res| ==> x <= res[k];

    assert forall t: int :: k <= t < |res| ==> x <= res[t] by {
      forall t: int | k <= t < |res|
        ensures x <= res[t]
      {
        assert k < |res|;
        assert x <= res[k];
        if t == k {
        } else {
          assert k < t;
          assert res[k] <= res[t];
        }
      }
    }

    var newRes := res[..k] + [x] + res[k..];
    assert |newRes| == |res| + 1;

    assert forall a: int, b: int :: 0 <= a < b < |newRes| ==> newRes[a] <= newRes[b] by {
      forall a: int, b: int | 0 <= a < b < |newRes|
        ensures newRes[a] <= newRes[b]
      {
        if b < k {
          assert newRes[a] == res[a];
          assert newRes[b] == res[b];
          assert res[a] <= res[b];
        } else if b == k {
          assert a < k;
          assert newRes[a] == res[a];
          assert newRes[b] == x;
          assert res[a] <= x;
        } else {
          assert k < b;
          assert b - 1 < |res|;
          assert newRes[b] == res[b - 1];
          if a < k {
            assert newRes[a] == res[a];
            assert a < b - 1;
            assert res[a] <= res[b - 1];
          } else if a == k {
            assert newRes[a] == x;
            assert k <= b - 1 < |res|;
            assert x <= res[b - 1];
          } else {
            assert k < a;
            assert newRes[a] == res[a - 1];
            assert 0 <= a - 1 < b - 1 < |res|;
            assert res[a - 1] <= res[b - 1];
          }
        }
      }
    }

    assert res == res[..k] + res[k..];
    assert multiset(newRes) == multiset(res) + multiset([x]);
    assert multiset(newRes) + multiset(rest) == multiset(res) + multiset(oldRest);
    assert multiset(newRes) + multiset(rest) == multiset(inputs[..]);

    res := newRes;
  }

  assert |rest| == 0;
  assert rest == [];
  assert multiset(res) == multiset(inputs[..]);

  sorted := new string[|res|](i => if 0 <= i && i < |res| then res[i] else "");
  assert sorted.Length == |res|;
  assert forall i: int :: 0 <= i < sorted.Length ==> sorted[i] == res[i];
  assert forall i: int :: 0 <= i < |res| ==> sorted[..][i] == res[i] by {
    forall i: int | 0 <= i < |res|
      ensures sorted[..][i] == res[i]
    {
      assert sorted[..][i] == sorted[i];
      assert sorted[i] == res[i];
    }
  }
  assert sorted[..] == res;

  assert forall i: int, j: int :: 0 <= i < j < sorted.Length ==> sorted[i] <= sorted[j] by {
    forall i: int, j: int | 0 <= i < j < sorted.Length
      ensures sorted[i] <= sorted[j]
    {
      assert sorted[i] == res[i];
      assert sorted[j] == res[j];
      assert res[i] <= res[j];
    }
  }

  assert multiset(inputs[..]) == multiset(sorted[..]);
}