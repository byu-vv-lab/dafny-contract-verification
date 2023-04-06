method BinarySearch(a: array<int>, key: int) returns (index: int)
	requires forall i, j | 0 <= i < a.Length && 0 <= j < a.Length :: i <= j ==> a[i] <= a[j]
	ensures 0 <= index < a.Length ==> a[index] == key
	ensures index <	0 ==> forall k :: 0	<= k < a.Length	==>	a[k] != key;
// {
// 	var low := 0;
// 	var high :=	a.Length;
// 	while (low < high)
// 		invariant 0	<= low <= high <= a.Length;
// 		invariant forall i :: 0	<= i < a.Length	&& !(low <=	i <	high) ==> a[i] != key;
// 	{
// 		var mid := (low	+ high)	/ 2;
// 		if (a[mid] < key) {
// 			low	:= mid + 1;
// 		}
// 		else if (key < a[mid])	{
// 			high :=	mid;
// 		}
// 		else {
// 			return mid;
// 		}
// 	}
// 	return -1;
// }

method absolute_value(n : int) returns (result : int)
    ensures n < 0 ==> result == -1 * n
{
    if (n < 0) {
        return -1 * n;
    } else {
        return n;
    }
}

method inconsistent(a : bool, b : bool) returns (x : bool, y : bool)
    ensures a ==> x
    ensures a && b ==> y
    ensures !b ==> !y
{
    x := false;
    y := true;
    if (a && b) {
        return true, true;
    } else if (a && !b) {
        return true, false;
    } else if (!b) {
        return true, false;
    }
}

method soconfused(x : int, y : int) returns (a : int, b : int)
    ensures x + y > 20 ==> a == 0
    ensures x + y < 20 ==> b == 0
{
    a := 42;
    b := 42;
    if (x + y > 20) {
        a := 0;
    }
    if (x + y < 20) {
        b := 0;
    }
}