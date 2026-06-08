function sum(values: seq<real>): real
{
  if |values| == 0 then 0.0
  else values[0] + sum(values[1..])
}

method p_4_5_analyse_floats_seq(values: seq<real>) returns (average: real, min: real, max: real, range: real)
	requires 0 < |values|
	ensures average == (sum(values) / |values| as real)
	ensures forall v :: v in values ==> min <= v
	ensures forall v :: v in values ==> max >= v
	ensures range == max - min
	ensures exists v :: v in values && min == v
	ensures exists v :: v in values && max == v
{
  if |values| == 1 {
    average := values[0];
    min := values[0];
    max := values[0];
    range := 0.0;

    assert values[0] in values;
    assert values[1..] == [];
    assert sum(values[1..]) == 0.0;
    assert sum(values) == values[0] + sum(values[1..]);
    assert sum(values) == values[0];
    assert (|values| as real) == 1.0;
    assert average == sum(values) / (|values| as real);

    forall v: real | v in values
      ensures v == values[0]
    {
      var k: int :| 0 <= k < |values| && values[k] == v;
      assert k == 0;
    }

    assert exists v: real :: v in values && min == v;
    assert exists v: real :: v in values && max == v;
  } else {
    assert 1 < |values|;
    assert 0 < |values[1..]|;

    var tailAverage, tailMin, tailMax, tailRange := p_4_5_analyse_floats_seq(values[1..]);
    var tailLen: real := |values[1..]| as real;
    var len: real := |values| as real;
    assert tailLen > 0.0;
    assert tailLen != 0.0;
    assert |values| == 1 + |values[1..]|;
    assert len == 1.0 + tailLen;

    assert tailAverage == sum(values[1..]) / tailLen;
    assert (sum(values[1..]) / tailLen) * tailLen == sum(values[1..]);
    assert tailAverage * tailLen == sum(values[1..]);

    average := (values[0] + tailAverage * tailLen) / len;

    assert sum(values) == values[0] + sum(values[1..]);
    calc {
      average;
      ==
      (values[0] + tailAverage * tailLen) / len;
      ==
      (values[0] + sum(values[1..])) / len;
      ==
      sum(values) / len;
      ==
      sum(values) / (|values| as real);
    }

    var headIsMin := values[0] <= tailMin;
    if headIsMin {
      min := values[0];
    } else {
      min := tailMin;
    }

    var headIsMax := values[0] >= tailMax;
    if headIsMax {
      max := values[0];
    } else {
      max := tailMax;
    }

    range := max - min;

    assert values[0] in values;

    forall v: real | v in values[1..]
      ensures v in values
    {
      var k: int :| 0 <= k < |values[1..]| && values[1..][k] == v;
      assert 0 <= k + 1 < |values|;
      assert values[1..][k] == values[k + 1];
      assert values[k + 1] == v;
      assert v in values;
    }

    forall v: real | v in values
      ensures v == values[0] || v in values[1..]
    {
      var k: int :| 0 <= k < |values| && values[k] == v;
      if k == 0 {
        assert v == values[0];
      } else {
        assert 0 <= k - 1 < |values[1..]|;
        assert values[1..][k - 1] == values[k];
        assert values[1..][k - 1] == v;
        assert v in values[1..];
      }
    }

    forall v: real | v in values
      ensures min <= v
    {
      if v == values[0] {
        if headIsMin {
          assert min == values[0];
        } else {
          assert min == tailMin;
          assert !(values[0] <= tailMin);
          assert tailMin < values[0];
          assert tailMin <= values[0];
        }
      } else {
        assert v in values[1..];
        if headIsMin {
          assert min == values[0];
          assert values[0] <= tailMin;
          assert tailMin <= v;
        } else {
          assert min == tailMin;
          assert tailMin <= v;
        }
      }
    }

    forall v: real | v in values
      ensures max >= v
    {
      if v == values[0] {
        if headIsMax {
          assert max == values[0];
        } else {
          assert max == tailMax;
          assert !(values[0] >= tailMax);
          assert values[0] < tailMax;
          assert tailMax >= values[0];
        }
      } else {
        assert v in values[1..];
        if headIsMax {
          assert max == values[0];
          assert values[0] >= tailMax;
          assert tailMax >= v;
        } else {
          assert max == tailMax;
          assert tailMax >= v;
        }
      }
    }

    if headIsMin {
      assert min == values[0];
      assert values[0] in values && min == values[0];
      assert exists v: real :: v in values && min == v;
    } else {
      assert min == tailMin;
      var w: real :| w in values[1..] && tailMin == w;
      assert w in values;
      assert w in values && min == w;
      assert exists v: real :: v in values && min == v;
    }

    if headIsMax {
      assert max == values[0];
      assert values[0] in values && max == values[0];
      assert exists v: real :: v in values && max == v;
    } else {
      assert max == tailMax;
      var w: real :| w in values[1..] && tailMax == w;
      assert w in values;
      assert w in values && max == w;
      assert exists v: real :: v in values && max == v;
    }
  }
}