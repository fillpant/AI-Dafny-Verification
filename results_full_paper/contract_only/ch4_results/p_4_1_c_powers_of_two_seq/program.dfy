function pow(base: int, exp: int): int
  requires  0 <= exp
  decreases exp
{
  if exp == 0 then 1 else base * pow(base, exp - 1)
}

method p_4_1_c_powers_of_two_seq() returns (powers: seq<int>)
	ensures |powers| == 21
	ensures forall i :: 0 <= i < |powers| ==> powers[i] == pow(2, i)
{
  powers := [
    1,
    2,
    4,
    8,
    16,
    32,
    64,
    128,
    256,
    512,
    1024,
    2048,
    4096,
    8192,
    16384,
    32768,
    65536,
    131072,
    262144,
    524288,
    1048576
  ];

  assert |powers| == 21;

  assert pow(2, 0) == 1;
  assert pow(2, 1) == 2 * pow(2, 0);
  assert pow(2, 1) == 2;
  assert pow(2, 2) == 2 * pow(2, 1);
  assert pow(2, 2) == 4;
  assert pow(2, 3) == 2 * pow(2, 2);
  assert pow(2, 3) == 8;
  assert pow(2, 4) == 2 * pow(2, 3);
  assert pow(2, 4) == 16;
  assert pow(2, 5) == 2 * pow(2, 4);
  assert pow(2, 5) == 32;
  assert pow(2, 6) == 2 * pow(2, 5);
  assert pow(2, 6) == 64;
  assert pow(2, 7) == 2 * pow(2, 6);
  assert pow(2, 7) == 128;
  assert pow(2, 8) == 2 * pow(2, 7);
  assert pow(2, 8) == 256;
  assert pow(2, 9) == 2 * pow(2, 8);
  assert pow(2, 9) == 512;
  assert pow(2, 10) == 2 * pow(2, 9);
  assert pow(2, 10) == 1024;
  assert pow(2, 11) == 2 * pow(2, 10);
  assert pow(2, 11) == 2048;
  assert pow(2, 12) == 2 * pow(2, 11);
  assert pow(2, 12) == 4096;
  assert pow(2, 13) == 2 * pow(2, 12);
  assert pow(2, 13) == 8192;
  assert pow(2, 14) == 2 * pow(2, 13);
  assert pow(2, 14) == 16384;
  assert pow(2, 15) == 2 * pow(2, 14);
  assert pow(2, 15) == 32768;
  assert pow(2, 16) == 2 * pow(2, 15);
  assert pow(2, 16) == 65536;
  assert pow(2, 17) == 2 * pow(2, 16);
  assert pow(2, 17) == 131072;
  assert pow(2, 18) == 2 * pow(2, 17);
  assert pow(2, 18) == 262144;
  assert pow(2, 19) == 2 * pow(2, 18);
  assert pow(2, 19) == 524288;
  assert pow(2, 20) == 2 * pow(2, 19);
  assert pow(2, 20) == 1048576;

  forall i | 0 <= i < |powers|
    ensures powers[i] == pow(2, i)
  {
    if i == 0 {
      assert powers[i] == 1;
      assert pow(2, i) == 1;
    } else if i == 1 {
      assert powers[i] == 2;
      assert pow(2, i) == 2;
    } else if i == 2 {
      assert powers[i] == 4;
      assert pow(2, i) == 4;
    } else if i == 3 {
      assert powers[i] == 8;
      assert pow(2, i) == 8;
    } else if i == 4 {
      assert powers[i] == 16;
      assert pow(2, i) == 16;
    } else if i == 5 {
      assert powers[i] == 32;
      assert pow(2, i) == 32;
    } else if i == 6 {
      assert powers[i] == 64;
      assert pow(2, i) == 64;
    } else if i == 7 {
      assert powers[i] == 128;
      assert pow(2, i) == 128;
    } else if i == 8 {
      assert powers[i] == 256;
      assert pow(2, i) == 256;
    } else if i == 9 {
      assert powers[i] == 512;
      assert pow(2, i) == 512;
    } else if i == 10 {
      assert powers[i] == 1024;
      assert pow(2, i) == 1024;
    } else if i == 11 {
      assert powers[i] == 2048;
      assert pow(2, i) == 2048;
    } else if i == 12 {
      assert powers[i] == 4096;
      assert pow(2, i) == 4096;
    } else if i == 13 {
      assert powers[i] == 8192;
      assert pow(2, i) == 8192;
    } else if i == 14 {
      assert powers[i] == 16384;
      assert pow(2, i) == 16384;
    } else if i == 15 {
      assert powers[i] == 32768;
      assert pow(2, i) == 32768;
    } else if i == 16 {
      assert powers[i] == 65536;
      assert pow(2, i) == 65536;
    } else if i == 17 {
      assert powers[i] == 131072;
      assert pow(2, i) == 131072;
    } else if i == 18 {
      assert powers[i] == 262144;
      assert pow(2, i) == 262144;
    } else if i == 19 {
      assert powers[i] == 524288;
      assert pow(2, i) == 524288;
    } else {
      assert i == 20;
      assert powers[i] == 1048576;
      assert pow(2, i) == 1048576;
    }
  }
}