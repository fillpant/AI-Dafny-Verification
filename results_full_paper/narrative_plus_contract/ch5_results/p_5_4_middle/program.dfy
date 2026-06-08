method p_5_4_middle(str: string) returns (middle_str: string)
	requires 0 < |str|
	ensures if |str| % 2 == 1 then |middle_str| == 1 else |middle_str| == 2
	ensures if |str| % 2 == 1 then middle_str[0] == str[|str| / 2] else middle_str == str[|str| / 2 - 1 .. (|str| / 2) + 1]
{
  var n := |str|;
  var mid := n / 2;

  if n % 2 == 1 {
    assert n == 2 * mid + 1;
    assert mid < n;
    assert mid + 1 <= n;
    middle_str := str[mid .. mid + 1];
    assert |middle_str| == 1;
    assert middle_str[0] == str[mid];
  } else {
    assert n % 2 == 0;
    assert n == 2 * mid;
    assert mid > 0;
    assert mid + 1 <= n;
    middle_str := str[mid - 1 .. mid + 1];
    assert |middle_str| == 2;
  }
}