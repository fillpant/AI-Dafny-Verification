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
    range := max - min;

    assert values == [values[0]];
    assert values[1..] == [];
    assert sum(values[1..]) == 0.0;
    assert sum(values) == values[0] + sum(values[1..]);
    assert sum(values) == values[0];
    assert (|values| as real) == 1.0;
    assert average == sum(values) / (|values| as real);

    assert values[0] in values;

    forall v | v in values
      ensures min <= v
    {
      assert v == values[0];
    }

    forall v | v in values
      ensures max >= v
    {
      assert v == values[0];
    }

    assert exists v :: v in values && min == v;
    assert exists v :: v in values && max == v;
  } else {
    assert 1 < |values|;
    var tail := values[1..];
    assert 0 < |tail|;
    assert |values| == |tail| + 1;
    assert values == [values[0]] + tail;
    assert forall v :: (v in values) <==> (v == values[0] || v in tail);

    var tailAverage, tailMin, tailMax, tailRange := p_4_5_analyse_floats_seq(tail);
    assert tailAverage == sum(tail) / (|tail| as real);
    assert tailRange == tailMax - tailMin;

    var tailLength := |tail| as real;
    assert tailLength == (|tail| as real);
    assert tailLength != 0.0;
    assert (|values| as real) == tailLength + 1.0;

    average := (values[0] + tailAverage * tailLength) / (|values| as real);

    calc {
      tailAverage * tailLength;
      == {
        assert tailAverage == sum(tail) / tailLength;
      }
      (sum(tail) / tailLength) * tailLength;
      == {
        assert tailLength != 0.0;
      }
      sum(tail);
    }

    assert values[1..] == tail;
    assert sum(values) == values[0] + sum(values[1..]);
    assert sum(values) == values[0] + sum(tail);

    calc {
      average;
      == {
      }
      (values[0] + tailAverage * tailLength) / (|values| as real);
      == {
        assert tailAverage * tailLength == sum(tail);
      }
      (values[0] + sum(tail)) / (|values| as real);
      == {
        assert sum(values) == values[0] + sum(tail);
      }
      sum(values) / (|values| as real);
    }

    if values[0] <= tailMin {
      min := values[0];
      assert values[0] in values;
      assert exists v :: v in values && min == v;
    } else {
      min := tailMin;
      ghost var w: real :| w in tail && tailMin == w;
      assert w in values;
      assert exists v :: v in values && min == v;
    }

    if values[0] >= tailMax {
      max := values[0];
      assert values[0] in values;
      assert exists v :: v in values && max == v;
    } else {
      max := tailMax;
      ghost var w: real :| w in tail && tailMax == w;
      assert w in values;
      assert exists v :: v in values && max == v;
    }

    forall v | v in values
      ensures min <= v
    {
      if v == values[0] {
        if values[0] <= tailMin {
          assert min == values[0];
        } else {
          assert min == tailMin;
          assert tailMin < values[0];
        }
      } else {
        assert v in tail;
        assert tailMin <= v;
        if values[0] <= tailMin {
          assert min == values[0];
          assert values[0] <= v;
        } else {
          assert min == tailMin;
        }
      }
    }

    forall v | v in values
      ensures max >= v
    {
      if v == values[0] {
        if values[0] >= tailMax {
          assert max == values[0];
        } else {
          assert max == tailMax;
          assert tailMax > values[0];
        }
      } else {
        assert v in tail;
        assert tailMax >= v;
        if values[0] >= tailMax {
          assert max == values[0];
          assert values[0] >= v;
        } else {
          assert max == tailMax;
        }
      }
    }

    range := max - min;
  }
}