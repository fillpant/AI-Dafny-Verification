method hybrid_car_cost(new_car_cost: real, miles_per_year: real, gas_price: real, mpg: real, resale_value: real) returns (total_cost: real)
	requires 0.0 < mpg
	ensures total_cost == new_car_cost + (miles_per_year / mpg) * gas_price * 5.0 - resale_value
{
  total_cost := new_car_cost + (miles_per_year / mpg) * gas_price * 5.0 - resale_value;
}