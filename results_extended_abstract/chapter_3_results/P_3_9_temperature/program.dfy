method P_3_9_temperature (t: real, c: char) returns (s: string)
	requires (c == 'C' && t >= -273.15) || (c == 'F' && t >= -459.67)
	requires c == 'C' || c == 'F'
	ensures if c == 'C' then if t < 0.0 then s == "solid" else if t == 0.0 then s == "solid or liquid" else if 0.0 < t < 100.0 then s == "liquid" else if t == 100.0 then s == "liquid or gaseous" else s == "gaseous" else if t < 32.0 then s == "solid" else if t == 32.0 then s == "solid or liquid" else if 32.0 < t < 212.0 then s == "liquid" else if t == 212.0 then s == "liquid or gaseous" else s == "gaseous"
{
  if c == 'C' {
    if t < 0.0 {
      s := "solid";
    } else if t == 0.0 {
      s := "solid or liquid";
    } else if t < 100.0 {
      s := "liquid";
    } else if t == 100.0 {
      s := "liquid or gaseous";
    } else {
      s := "gaseous";
    }
  } else {
    if t < 32.0 {
      s := "solid";
    } else if t == 32.0 {
      s := "solid or liquid";
    } else if t < 212.0 {
      s := "liquid";
    } else if t == 212.0 {
      s := "liquid or gaseous";
    } else {
      s := "gaseous";
    }
  }
}