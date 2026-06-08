method p_6_2_e_remove_middle_seq(inputs: seq<int>) returns (result: seq<int>)
	requires |inputs| >= 1
	ensures |result| == if |inputs| % 2 == 1 then |inputs| - 1 else |inputs| - 2
	ensures |inputs| % 2 == 1 ==> forall i :: 0 <= i < |inputs| / 2 ==> result[i] == inputs[i] && forall j :: |inputs| / 2 <= j < |result| ==> result[j] == inputs[j + 1]
	ensures |inputs| % 2 == 0 ==> forall i :: 0 <= i < |inputs| / 2 - 1 ==> result[i] == inputs[i] && forall j :: |inputs| / 2 - 1 <= j < |result| ==> result[j] == inputs[j + 2]
{
  var n := |inputs|;
  if n % 2 == 1 {
    var m := n / 2;
    assert n == (n / 2) * 2 + n % 2;
    assert n == m * 2 + 1;
    assert m * 2 == 2 * m;
    assert n == 2 * m + 1;
    assert 0 <= m;
    assert m + 1 <= n;

    var left := inputs[..m];
    var right := inputs[m + 1..];
    result := left + right;

    assert |left| == m;
    assert |right| == n - (m + 1);
    assert |result| == |left| + |right|;
    assert |result| == n - 1;

    forall i | 0 <= i < m
      ensures result[i] == inputs[i]
    {
      assert i < |left|;
      assert result[i] == left[i];
      assert left[i] == inputs[i];
    }

    forall j | m <= j < |result|
      ensures result[j] == inputs[j + 1]
    {
      assert |left| == m;
      assert j >= |left|;
      assert 0 <= j - m;
      assert j < n - 1;
      assert j - m < n - (m + 1);
      assert j - m < |right|;
      assert j - |left| == j - m;
      assert result[j] == right[j - |left|];
      assert result[j] == right[j - m];
      assert right[j - m] == inputs[(m + 1) + (j - m)];
      assert (m + 1) + (j - m) == j + 1;
    }
  } else {
    var m := n / 2;
    assert 0 <= n % 2 < 2;
    assert n % 2 == 0;
    assert n == (n / 2) * 2 + n % 2;
    assert n == m * 2;
    assert m * 2 == 2 * m;
    assert n == 2 * m;
    assert 0 <= m;
    if m < 1 {
      assert m == 0;
      assert n == 0;
      assert false;
    }
    assert m >= 1;
    assert m - 1 >= 0;
    assert m + 1 <= n;

    var left := inputs[..(m - 1)];
    var right := inputs[m + 1..];
    result := left + right;

    assert |left| == m - 1;
    assert |right| == n - (m + 1);
    assert |result| == |left| + |right|;
    assert |result| == n - 2;

    forall i | 0 <= i < m - 1
      ensures result[i] == inputs[i]
    {
      assert i < |left|;
      assert result[i] == left[i];
      assert left[i] == inputs[i];
    }

    forall j | m - 1 <= j < |result|
      ensures result[j] == inputs[j + 2]
    {
      assert |left| == m - 1;
      assert j >= |left|;
      assert 0 <= j - (m - 1);
      assert j < n - 2;
      assert j - (m - 1) < n - (m + 1);
      assert j - (m - 1) < |right|;
      assert j - |left| == j - (m - 1);
      assert result[j] == right[j - |left|];
      assert result[j] == right[j - (m - 1)];
      assert right[j - (m - 1)] == inputs[(m + 1) + (j - (m - 1))];
      assert (m + 1) + (j - (m - 1)) == j + 2;
    }
  }
}