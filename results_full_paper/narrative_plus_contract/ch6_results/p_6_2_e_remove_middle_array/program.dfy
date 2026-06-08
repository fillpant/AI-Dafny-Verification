method p_6_2_e_remove_middle_array(inputs: array<int>) returns (result: array<int>)
	requires inputs.Length >= 1
	ensures result.Length == if inputs.Length % 2 == 1 then inputs.Length - 1 else inputs.Length - 2
	ensures inputs.Length % 2 == 1 ==> forall i :: 0 <= i < inputs.Length / 2 ==> result[i] == inputs[i] && forall j :: inputs.Length / 2 <= j < result.Length ==> result[j] == inputs[j + 1]
	ensures inputs.Length % 2 == 0 ==> forall i :: 0 <= i < inputs.Length / 2 - 1 ==> result[i] == inputs[i] && forall j :: inputs.Length / 2 - 1 <= j < result.Length ==> result[j] == inputs[j + 2]
{
  var n := inputs.Length;

  if n % 2 == 1 {
    var mid := n / 2;
    assert 0 <= n % 2 < 2;
    assert n == (n / 2) * 2 + n % 2;
    assert n == mid * 2 + 1;
    assert 0 <= mid;
    assert mid < n;

    result := new int[n - 1];
    assert result != inputs;
    assert result.Length == n - 1;
    assert result.Length == mid * 2;
    assert mid <= result.Length;

    var i := 0;
    while i < mid
      invariant 0 <= i <= mid
      invariant n == inputs.Length
      invariant result != inputs
      invariant result.Length == n - 1
      invariant mid <= result.Length
      invariant mid < n
      invariant forall k :: 0 <= k < i ==> result[k] == inputs[k]
    {
      assert 0 <= i < result.Length;
      assert 0 <= i < inputs.Length;
      result[i] := inputs[i];
      i := i + 1;
    }

    var j := mid;
    while j < result.Length
      invariant mid <= j <= result.Length
      invariant n == inputs.Length
      invariant result != inputs
      invariant result.Length == n - 1
      invariant mid <= result.Length
      invariant forall k :: 0 <= k < mid ==> result[k] == inputs[k]
      invariant forall k :: mid <= k < j ==> result[k] == inputs[k + 1]
    {
      assert 0 <= j < result.Length;
      assert 0 <= j + 1 < inputs.Length;
      result[j] := inputs[j + 1];
      j := j + 1;
    }

    assert mid == inputs.Length / 2;
    assert result.Length == inputs.Length - 1;
    assert result.Length == (if inputs.Length % 2 == 1 then inputs.Length - 1 else inputs.Length - 2);
    assert forall k :: 0 <= k < inputs.Length / 2 ==> result[k] == inputs[k];
    assert forall k :: inputs.Length / 2 <= k < result.Length ==> result[k] == inputs[k + 1];
    assert forall k :: 0 <= k < inputs.Length / 2 ==> result[k] == inputs[k] && (forall t :: inputs.Length / 2 <= t < result.Length ==> result[t] == inputs[t + 1]);
  } else {
    assert n % 2 != 1;
    assert 0 <= n % 2 < 2;
    assert n % 2 == 0;
    if n == 1 {
      assert n % 2 == 1;
      assert false;
    }
    assert n >= 2;

    var mid := n / 2;
    assert n == (n / 2) * 2 + n % 2;
    assert n == mid * 2;
    assert 1 <= mid;

    var left := mid - 1;
    assert 0 <= left;
    assert mid == left + 1;

    result := new int[n - 2];
    assert result != inputs;
    assert result.Length == n - 2;
    assert result.Length == left * 2;
    assert left <= result.Length;

    var i := 0;
    while i < left
      invariant 0 <= i <= left
      invariant n == inputs.Length
      invariant result != inputs
      invariant result.Length == n - 2
      invariant left <= result.Length
      invariant forall k :: 0 <= k < i ==> result[k] == inputs[k]
    {
      assert 0 <= i < result.Length;
      assert 0 <= i < inputs.Length;
      result[i] := inputs[i];
      i := i + 1;
    }

    var j := left;
    while j < result.Length
      invariant left <= j <= result.Length
      invariant n == inputs.Length
      invariant result != inputs
      invariant result.Length == n - 2
      invariant left <= result.Length
      invariant forall k :: 0 <= k < left ==> result[k] == inputs[k]
      invariant forall k :: left <= k < j ==> result[k] == inputs[k + 2]
    {
      assert 0 <= j < result.Length;
      assert 0 <= j + 2 < inputs.Length;
      result[j] := inputs[j + 2];
      j := j + 1;
    }

    assert left == inputs.Length / 2 - 1;
    assert result.Length == inputs.Length - 2;
    assert result.Length == (if inputs.Length % 2 == 1 then inputs.Length - 1 else inputs.Length - 2);
    assert forall k :: 0 <= k < inputs.Length / 2 - 1 ==> result[k] == inputs[k];
    assert forall k :: inputs.Length / 2 - 1 <= k < result.Length ==> result[k] == inputs[k + 2];
    assert forall k :: 0 <= k < inputs.Length / 2 - 1 ==> result[k] == inputs[k] && (forall t :: inputs.Length / 2 - 1 <= t < result.Length ==> result[t] == inputs[t + 2]);
  }
}