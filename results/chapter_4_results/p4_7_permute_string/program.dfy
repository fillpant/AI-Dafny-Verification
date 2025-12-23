method p4_7_permute_string(s: string) returns (permuted: string)
	ensures |permuted| == |s|
	ensures forall c :: c in s ==> c in permuted
	ensures forall c :: c in permuted ==> c in s
{
  permuted := s;
}