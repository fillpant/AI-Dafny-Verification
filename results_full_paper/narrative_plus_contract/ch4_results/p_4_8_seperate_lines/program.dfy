method p_4_8_seperate_lines(s: string) returns (chars: string)
	ensures |chars| == 2 * |s|
	ensures forall i :: 0 <= i < |s| ==> i % 2 == 1 ==> chars[i] == '\n'
	ensures forall i :: 0 <= i < |s| ==> i % 2 == 0 ==> chars[i] == s[i / 2]
{
  chars := seq(2 * |s|, i requires 0 <= i < 2 * |s| => if i % 2 == 0 then s[i / 2] else '\n');
}