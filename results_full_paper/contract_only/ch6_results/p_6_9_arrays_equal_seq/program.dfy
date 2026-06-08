method p_6_9_arrays_equal_seq(first: seq<int>, second: seq<int>) returns (are_equal: bool)
	ensures are_equal == (|first| == |second| && forall i :: 0 <= i < |first| ==> first[i] == second[i])
{
  if |first| != |second| {
    are_equal := false;
  } else {
    are_equal := true;
    var i := 0;
    while i < |first|
      invariant |first| == |second|
      invariant 0 <= i <= |first|
      invariant are_equal ==> forall j :: 0 <= j < i ==> first[j] == second[j]
      invariant !are_equal ==> exists j :: 0 <= j < i && first[j] != second[j]
      decreases |first| - i
    {
      if are_equal {
        if first[i] != second[i] {
          are_equal := false;
          assert 0 <= i < i + 1 && first[i] != second[i];
          assert exists j :: 0 <= j < i + 1 && first[j] != second[j];
        } else {
          assert first[i] == second[i];
          forall j | 0 <= j < i + 1
            ensures first[j] == second[j]
          {
            if j < i {
              assert first[j] == second[j];
            } else {
              assert j == i;
              assert first[j] == second[j];
            }
          }
        }
      } else {
        ghost var k :| 0 <= k < i && first[k] != second[k];
        assert 0 <= k < i + 1 && first[k] != second[k];
        assert exists j :: 0 <= j < i + 1 && first[j] != second[j];
      }
      i := i + 1;
    }

    assert i == |first|;
    if are_equal {
      assert forall j :: 0 <= j < |first| ==> first[j] == second[j];
    } else {
      assert exists j :: 0 <= j < |first| && first[j] != second[j];
      ghost var k :| 0 <= k < |first| && first[k] != second[k];
      assert !(forall j :: 0 <= j < |first| ==> first[j] == second[j]);
    }
  }
}