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
  var i := values.Length - 1;
  var total := values[i];
  min := values[i];
  max := values[i];

  assert values[i..] == [values[i]];
  assert sum(values[i..]) == values[i];
  assert forall v :: v in values[i..] ==> min <= v;
  assert forall v :: v in values[i..] ==> max >= v;
  assert min in values[i..];
  assert max in values[i..];

  while 0 < i
    invariant 0 <= i < values.Length
    invariant total == sum(values[i..])
    invariant forall v :: v in values[i..] ==> min <= v
    invariant forall v :: v in values[i..] ==> max >= v
    invariant min in values[i..]
    invariant max in values[i..]
    decreases i
  {
    var oldI := i;
    var oldMin := min;
    var oldMax := max;

    i := i - 1;
    var x := values[i];

    assert oldI == i + 1;
    assert values[i..] == [x] + values[oldI..];
    assert values[i..][0] == x;
    assert values[i..][1..] == values[oldI..];

    total := x + total;
    assert total == x + sum(values[oldI..]);
    assert sum(values[i..]) == x + sum(values[i..][1..]);
    assert sum(values[i..]) == total;

    if x < oldMin {
      min := x;
      assert min in values[i..];
      forall v | v in values[i..]
        ensures min <= v
      {
        if v == x {
        } else {
          assert v in values[oldI..];
          assert oldMin <= v;
          assert min < oldMin;
        }
      }
    } else {
      min := oldMin;
      assert min <= x;
      assert min in values[oldI..];
      assert min in values[i..];
      forall v | v in values[i..]
        ensures min <= v
      {
        if v == x {
        } else {
          assert v in values[oldI..];
          assert oldMin <= v;
        }
      }
    }

    if x > oldMax {
      max := x;
      assert max in values[i..];
      forall v | v in values[i..]
        ensures max >= v
      {
        if v == x {
        } else {
          assert v in values[oldI..];
          assert oldMax >= v;
          assert max > oldMax;
        }
      }
    } else {
      max := oldMax;
      assert max >= x;
      assert max in values[oldI..];
      assert max in values[i..];
      forall v | v in values[i..]
        ensures max >= v
      {
        if v == x {
        } else {
          assert v in values[oldI..];
          assert oldMax >= v;
        }
      }
    }
  }

  assert i == 0;
  assert values[i..] == values[..];
  assert total == sum(values[..]);
  assert min in values[..];
  assert max in values[..];

  average := total / (values.Length as real);
  range := max - min;
}