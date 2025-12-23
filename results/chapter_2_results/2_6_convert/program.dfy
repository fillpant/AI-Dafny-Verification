method convert(x: real) returns (miles: real, feet: real, inches: real)
	ensures x / 0.000621371 == miles
	ensures x / 3.28084 == feet
	ensures x / 39.3701 == inches
{
  miles := x / 0.000621371;
  feet := x / 3.28084;
  inches := x / 39.3701;
}