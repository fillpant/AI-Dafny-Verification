function sum(values: seq<real>): real
{
  if |values| == 0 then 0.0
  else values[0] + sum(values[1..])
}

method p4_5_analyze_floats(values: seq<real>) returns (average: real, min: real, max: real, range: real)
	requires 0 < |values|
	ensures average == (sum(values) / |values| as real)
	ensures forall v :: v in values ==> min <= v
	ensures forall v :: v in values ==> max >= v
	ensures range == max - min
	ensures exists v :: v in values && min == v
	ensures exists v :: v in values && max == v
{
  var s: real := 0.0;
  min := values[0];
  max := values[0];
  var i: int := 0;
  while i < |values|
    invariant 0 <= i <= |values|
    invariant s == sum(values[..i])
    invariant forall v :: v in values[..i] ==> min <= v
    invariant forall v :: v in values[..i] ==> max >= v
    invariant i == 0 || exists v :: v in values[..i] && min == v
    invariant i == 0 || exists v :: v in values[..i] && max == v
  {
    s := s + values[i];
    if values[i] < min {
      min := values[i];
    }
    if values[i] > max {
      max := values[i];
    }
    i := i + 1;
  }
  average := s / (|values| as real);
  range := max - min;
}