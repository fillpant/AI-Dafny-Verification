function sum(values: seq<real>): real
{
  if |values| == 0 then 0.0
  else values[0] + sum(values[1..])
}

method p_4_5_analyse_floats_array(values: array<real>) returns (average: real, min: real, max: real, range: real)
	requires 0 < values.Length
	ensures average == (sum(values[..]) / values.Length as real)
	ensures forall v :: v in values[..] ==> min <= v
	ensures forall v :: v in values[..] ==> max >= v
	ensures range == max - min
	ensures exists v :: v in values[..] && min == v
	ensures exists v :: v in values[..] && max == v
{
  var n := values.Length;

  var total := 0.0;
  var i := n;
  while 0 < i
    invariant 0 <= i <= n
    invariant total == sum(values[i..n])
  {
    i := i - 1;
    assert 0 <= i < n;
    assert total == sum(values[i + 1..n]);
    assert |values[i..n]| > 0;
    assert (values[i..n])[0] == values[i];
    assert (values[i..n])[1..] == values[i + 1..n];
    assert sum(values[i..n]) == values[i] + sum(values[i + 1..n]);
    total := values[i] + total;
    assert total == sum(values[i..n]);
  }
  assert i == 0;
  assert values[0..n] == values[..];
  assert total == sum(values[..]);

  min := values[0];
  max := values[0];
  var minIndex := 0;
  var maxIndex := 0;
  i := 1;
  while i < n
    invariant 1 <= i <= n
    invariant forall k: int :: 0 <= k < i ==> min <= values[k]
    invariant forall k: int :: 0 <= k < i ==> max >= values[k]
    invariant 0 <= minIndex < i
    invariant min == values[minIndex]
    invariant 0 <= maxIndex < i
    invariant max == values[maxIndex]
  {
    var x := values[i];
    if x < min {
      min := x;
      minIndex := i;
    }
    if x > max {
      max := x;
      maxIndex := i;
    }
    i := i + 1;
  }
  assert i == n;
  assert forall k: int :: 0 <= k < n ==> min <= values[k];
  assert forall k: int :: 0 <= k < n ==> max >= values[k];

  average := total / (n as real);
  range := max - min;
  assert n == values.Length;
  assert average == sum(values[..]) / (values.Length as real);

  forall v: real | v in values[..]
    ensures min <= v
  {
    assert exists k: int :: 0 <= k < |values[..]| && (values[..])[k] == v;
    var k: int :| 0 <= k < |values[..]| && (values[..])[k] == v;
    assert |values[..]| == n;
    assert (values[..])[k] == values[k];
    assert v == values[k];
    assert min <= values[k];
  }
  forall v: real | v in values[..]
    ensures max >= v
  {
    assert exists k: int :: 0 <= k < |values[..]| && (values[..])[k] == v;
    var k: int :| 0 <= k < |values[..]| && (values[..])[k] == v;
    assert |values[..]| == n;
    assert (values[..])[k] == values[k];
    assert v == values[k];
    assert max >= values[k];
  }

  assert 0 <= minIndex < |values[..]|;
  assert (values[..])[minIndex] == min;
  assert min in values[..];
  assert exists v: real :: (v in values[..]) && min == v;

  assert 0 <= maxIndex < |values[..]|;
  assert (values[..])[maxIndex] == max;
  assert max in values[..];
  assert exists v: real :: (v in values[..]) && max == v;
}