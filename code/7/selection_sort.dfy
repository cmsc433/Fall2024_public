predicate sorted(a: array<int>, l: int, u: int)
  reads a
  requires 0 <=l <=u <= a.Length
{
  forall i, j :: l <= i < j < u  ==> a[i] <= a[j]
}

method selection_sort_nested(a: array<int>) 
  modifies a
  ensures sorted(a, 0, a.Length)
  ensures multiset(old(a[..])) == multiset(a[..])
{
  var n := 0;
  while (n != a.Length)
    invariant 0 <= n <= a.Length
    invariant forall i,j :: 0 <= i < n <= j < a.Length ==> a[i] <= a[j] 
    invariant forall k1, k2 :: 0 <= k1 < k2 < n ==> a[k1] <= a[k2] 
    invariant multiset(old(a[..])) == multiset(a[..])
  {
    var mindex := n;
    var m := n + 1;
    while (m != a.Length)
      invariant n <= m <= a.Length
      invariant n <= mindex < m <= a.Length
      invariant forall i :: n <= i < m ==> a[mindex] <= a[i] 
    {
      if (a[m] < a[mindex]) {
        mindex := m;
      }
      m := m + 1;
    }
    a[n], a[mindex] := a[mindex], a[n] ;
    n := n + 1;
  }
}

method findMin(a: array<int>, lo:nat) returns (index:nat)
  requires a.Length > 0
  requires lo < a.Length
  ensures lo<=index < a.Length
  ensures forall j:nat:: lo <= j < a.Length ==> a[index] <= a[j]
{
  index := lo;
  var i := lo;
  while i < a.Length
  invariant lo <= i <= a.Length
  invariant lo <= index <  a.Length
  invariant forall j:nat:: lo<=j < i ==> a[index] <= a[j]
  {
    if a[i] < a[index]{
      index := i;
    }
    i:= i + 1;
  }
}
method selection_sort(a: array<int>)
  modifies a
  ensures sorted(a,0,a.Length)
  requires 0 < a.Length
  ensures multiset(a[..])==multiset(old(a[..]) )
{
  var i := 0;
  while i < a.Length
    invariant 0 <= i <= a.Length
    invariant forall k, l :: 0 <= k < i <= l < a.Length ==> a[k] <= a[l]
    //elements in the lower part of the array are no greater than the elements 
    // in the upper part
    // an essential property of the selection sort algorithm.
    invariant sorted(a,0,i)
    invariant multiset(a[..]) == multiset(old(a[..]))
  {
    var j := findMin(a, i);
    if(i != j) {
      a[i],a[j] := a[j], a[i];
    }
    i := i + 1;
  }
  assert i == a.Length;
}

method Main() {
  var a := new int[5][9, 14, 6, 1, 8];
  var m := findMin(a, 0);
  print m, "\n";
  selection_sort(a);
  var k := 0;
  while(k < a.Length) { print a[k], ","; k := k+1;}
  print "\n";
}