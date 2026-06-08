method p_4_2_d_adjacent_duplicates_array_without_4th_ensures(inputs: array<int>) returns (duplicates: array<int>)
	ensures forall d :: d in duplicates[..] ==> d in inputs[..]
	ensures forall i :: 0 <= i < inputs.Length - 1 && inputs[i] == inputs[i + 1] ==> inputs[i] in duplicates[..]
	ensures forall d :: d in duplicates[..] ==> exists i :: 0 <= i < inputs.Length - 1 && inputs[i] == inputs[i + 1] && inputs[i] == d
{
  var n := inputs.Length;
  var s: seq<int> := [];
  var i := 0;

  while i < n - 1
    invariant n == inputs.Length
    invariant 0 <= i <= n
    invariant forall d :: d in s ==> exists k :: 0 <= k < i && k < n - 1 && inputs[k] == inputs[k + 1] && inputs[k] == d
    invariant forall k :: 0 <= k < i && k < n - 1 && inputs[k] == inputs[k + 1] ==> inputs[k] in s
  {
    var prev := s;

    if inputs[i] == inputs[i + 1] {
      s := s + [inputs[i]];
    }

    forall d | d in s
      ensures exists k :: 0 <= k < i + 1 && k < n - 1 && inputs[k] == inputs[k + 1] && inputs[k] == d
    {
      if d in prev {
        var k :| 0 <= k < i && k < n - 1 && inputs[k] == inputs[k + 1] && inputs[k] == d;
        assert 0 <= k < i + 1;
      } else {
        if inputs[i] == inputs[i + 1] {
          assert s == prev + [inputs[i]];
          assert d == inputs[i];
          assert 0 <= i < i + 1;
          assert i < n - 1;
        } else {
          assert s == prev;
          assert d in prev;
        }
      }
    }

    forall k | 0 <= k < i + 1 && k < n - 1 && inputs[k] == inputs[k + 1]
      ensures inputs[k] in s
    {
      if k < i {
        assert inputs[k] in prev;
        if inputs[i] == inputs[i + 1] {
          assert s == prev + [inputs[i]];
          assert inputs[k] in s;
        } else {
          assert s == prev;
          assert inputs[k] in s;
        }
      } else {
        assert k == i;
        assert inputs[i] == inputs[i + 1];
        assert s == prev + [inputs[i]];
        assert inputs[k] == inputs[i];
        assert inputs[k] in s;
      }
    }

    i := i + 1;
  }

  assert i >= n - 1;

  duplicates := new int[|s|];
  assert duplicates.Length == |s|;
  assert duplicates != inputs;

  var j := 0;
  while j < |s|
    invariant n == inputs.Length
    invariant 0 <= i <= n
    invariant i >= n - 1
    invariant duplicates != inputs
    invariant duplicates.Length == |s|
    invariant 0 <= j <= |s|
    invariant duplicates[..j] == s[..j]
    invariant forall d :: d in s ==> exists k :: 0 <= k < i && k < n - 1 && inputs[k] == inputs[k + 1] && inputs[k] == d
    invariant forall k :: 0 <= k < i && k < n - 1 && inputs[k] == inputs[k + 1] ==> inputs[k] in s
  {
    duplicates[j] := s[j];
    assert duplicates[j] == s[j];
    assert duplicates[..j] == s[..j];
    assert duplicates[..j + 1] == s[..j + 1];
    j := j + 1;
  }

  assert j == |s|;
  assert duplicates[..] == duplicates[..j];
  assert s[..j] == s;
  assert duplicates[..] == s;

  forall d | d in duplicates[..]
    ensures d in inputs[..]
  {
    assert d in s;
    var k :| 0 <= k < i && k < n - 1 && inputs[k] == inputs[k + 1] && inputs[k] == d;
    assert n == inputs.Length;
    assert 0 <= k < inputs.Length;
    assert inputs[..][k] == inputs[k];
    assert d in inputs[..];
  }

  forall k | 0 <= k < inputs.Length - 1 && inputs[k] == inputs[k + 1]
    ensures inputs[k] in duplicates[..]
  {
    assert n == inputs.Length;
    assert !(i < n - 1);
    assert i >= n - 1;
    assert k < n - 1;
    assert k < i;
    assert inputs[k] in s;
    assert inputs[k] in duplicates[..];
  }

  forall d | d in duplicates[..]
    ensures exists k :: 0 <= k < inputs.Length - 1 && inputs[k] == inputs[k + 1] && inputs[k] == d
  {
    assert d in s;
    var k :| 0 <= k < i && k < n - 1 && inputs[k] == inputs[k + 1] && inputs[k] == d;
    assert n == inputs.Length;
    assert 0 <= k < inputs.Length - 1 && inputs[k] == inputs[k + 1] && inputs[k] == d;
  }
}