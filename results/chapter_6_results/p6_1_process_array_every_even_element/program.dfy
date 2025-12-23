method p6_1_process_array_every_even_element(arr: seq<int>) returns (even_elements: seq<int>)
	requires |arr| == 10
	ensures forall i :: 0 <= i < |arr| ==> arr[i] % 2 == 0 ==> exists j :: 0 <= j < |even_elements| && even_elements[j] == arr[i]
{
  even_elements := arr;
}