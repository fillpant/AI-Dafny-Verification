method p_5_4_middle(str: string) returns (middle_str: string)
	requires 0 < |str|
	ensures if |str| % 2 == 1 then |middle_str| == 1 else |middle_str| == 2
	ensures if |str| % 2 == 1 then middle_str[0] == str[|str| / 2] else middle_str == str[|str| / 2 - 1 .. (|str| / 2) + 1]
{
  var mid := |str| / 2;
  if |str| % 2 == 1 {
    middle_str := str[mid .. mid + 1];
    assert |middle_str| == 1;
    assert middle_str[0] == str[mid];
  } else {
    assert |str| % 2 == 0;
    assert 2 <= |str|;
    assert 1 <= mid;
    assert mid + 1 <= |str|;
    middle_str := str[mid - 1 .. mid + 1];
    assert |middle_str| == 2;
  }
}