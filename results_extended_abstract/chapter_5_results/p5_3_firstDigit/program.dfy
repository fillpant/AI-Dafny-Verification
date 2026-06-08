function intToSeq(n: int) : seq<int>
  requires n >= 0
  ensures forall d :: d in intToSeq(n) ==> 0 <= d < 10
{
  if n < 10 then [n]
  else intToSeq(n / 10) + [n % 10]
}

method p5_3_firstDigit(n: int) returns (first: int)
	requires 0 <= n
	ensures 0 <= first < 10
	ensures intToSeq(n)[0] == first
{
  if n < 10 {
    first := n;
  } else {
    first := p5_3_firstDigit(n / 10);
  }
}