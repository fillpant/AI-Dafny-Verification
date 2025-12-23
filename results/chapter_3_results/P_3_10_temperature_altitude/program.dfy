method P_3_10_temperature_altitude (t: real, a: nat) returns (s: string)
	requires t >= -273.15 && a <= 10000
	ensures if t < 0.0 then s == "solid" else if t == 0.0 then s == "solid or liquid" else if 0.0 < t < 100.0 - (a as real / 300.0) then s == "liquid" else if t == 100.0 - (a as real / 300.0) then s == "liquid or gaseous" else s == "gaseous"
{
  var bp := 100.0 - (a as real / 300.0);
  if t < 0.0 {
    s := "solid";
  } else if t == 0.0 {
    s := "solid or liquid";
  } else if t < bp {
    s := "liquid";
  } else if t == bp {
    s := "liquid or gaseous";
  } else {
    s := "gaseous";
  }
}