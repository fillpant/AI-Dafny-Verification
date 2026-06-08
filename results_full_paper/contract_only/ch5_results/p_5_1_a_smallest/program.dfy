method p_5_1_a_smallest(x: real, y: real, z: real) returns (smallest: real)
	ensures smallest <= x && smallest <= y && smallest <= z
	ensures smallest == x || smallest == y || smallest == z
{
  if x <= y {
    if x <= z {
      smallest := x;
    } else {
      smallest := z;
    }
  } else {
    if y <= z {
      smallest := y;
    } else {
      smallest := z;
    }
  }
}