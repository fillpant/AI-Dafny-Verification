method p_6_9_arrays_equal_seq(first: seq<int>, second: seq<int>) returns (are_equal: bool)
	ensures are_equal == (|first| == |second| && forall i :: 0 <= i < |first| ==> first[i] == second[i])
{
  if |first| != |second| {
    are_equal := false;
    return;
  }

  are_equal := true;
  var i := 0;
  while i < |first|
    invariant |first| == |second|
    invariant 0 <= i <= |first|
    invariant are_equal
    invariant forall j :: 0 <= j < i ==> first[j] == second[j]
  {
    if first[i] != second[i] {
      are_equal := false;
      assert 0 <= i < |first|;
      assert !(forall j :: 0 <= j < |first| ==> first[j] == second[j]);
      return;
    }

    assert forall j :: 0 <= j < i + 1 ==> first[j] == second[j] by {
      forall j | 0 <= j < i + 1
        ensures first[j] == second[j]
      {
        if j < i {
        } else {
          assert j == i;
        }
      }
    }
    i := i + 1;
  }

  assert i == |first|;
  assert forall j :: 0 <= j < |first| ==> first[j] == second[j];
}