predicate sorted(a: array<int>)
   reads a
{
   forall j, k :: 0 <= j < k < a.Length ==> a[j] <= a[k]
}
method BinarySearch(a: array<int>, value: int) returns (index: int)
    requires 0 <= a.Length && sorted(a)
    ensures 0 <= index ==> index < a.Length && a[index] == value
    ensures index < 0 ==> forall k :: 0 <= k < a.Length ==> a[k] != value
{
    var lo := 0;
    var hi := a.Length;
    while lo < hi
        invariant 0 <= lo <= hi <= a.Length
        //invariant forall i :: 0 <= i < a.Length && !(lo <= i < hi) ==> a[i] != value
        invariant forall i:int::0<= i < lo ==>a[i] != value
        invariant forall i:int::hi <= i < a.Length ==>a[i] != value
    {
        //var mid := (lo + hi)/2;
        var mid := lo + (hi-lo)/2;
        if a[mid] > value
        {
            hi := mid;
        }else if a[mid] < value{
            lo := mid+1;
        }else{
            return mid;
        }
    }
    return -1;
}
