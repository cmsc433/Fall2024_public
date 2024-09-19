method QuickSort(a:array<int>)
  modifies a
  ensures forall i,j:: 0 <= i <j< a.Length ==> a[i] <= a[j]
  ensures multiset(a[..]) ==old( multiset(a[..]))
{
  QuickSortAux(a,0,a.Length);
}

method  QuickSortAux(a:array<int>, lo:int, hi:int)
  requires 0 <= lo <= hi <= a.Length
  modifies a
  ensures forall i,j:: lo <= i < j < hi==>a[i] <= a[j]
  ensures SwapFrame(a, lo, hi)
  requires SplitPoint(a, lo) && SplitPoint(a, hi)
  ensures SplitPoint(a, lo) && SplitPoint(a, hi)
  decreases hi - lo
{
  if 2 <= hi-lo{
    var p:= Partition(a,lo,hi);
    QuickSortAux(a,lo, p);
    QuickSortAux(a, p+1, hi);
  }
}
twostate predicate SwapFrame(a: array<int>, lo: int, hi: int)
  requires 0 <= lo <= hi <= a.Length
  reads a
{
  (forall i :: 0 <= i < lo || hi <= i < a.Length ==>
                 a[i] == old(a[i])) &&
  multiset(a[..]) == old(multiset(a[..]))
}

ghost predicate SplitPoint(a: array<int>, n: int)
  requires 0 <= n <= a.Length
  reads a
{
  forall i, j :: 0 <= i < n <= j < a.Length ==> a[i] <= a[j]
}

method Partition(a:array<int>, lo:int, hi:int) returns (p:int)
  requires 0 <= lo < hi<= a.Length
  requires SplitPoint(a, lo) && SplitPoint(a, hi)
  modifies a
  ensures lo <= p < hi
  ensures forall i :: lo <= i < p ==> a[i] < a[p]
  ensures forall i :: p <= i < hi ==> a[i] >= a[p]
  ensures SplitPoint(a, lo) && SplitPoint(a, hi)
  ensures SwapFrame(a, lo, hi)
{
  var pivot := a[lo];
  var m,n := lo+1, hi;
  while m < n
    invariant lo + 1 <= m <= n <= hi
    invariant a[lo] == pivot
    invariant forall i::lo+1 <= i < m ==>a[i] < pivot
    invariant forall i::n <= i < hi ==>a[i] >= pivot
    invariant SplitPoint(a, lo) && SplitPoint(a, hi)
    invariant SwapFrame(a, lo, hi)
  {
    if a[m] < pivot{
      m := m + 1;

    }else{
      a[m], a[n-1] := a[n-1],a[m];
      n := n -1;
    }
  }
  a[lo], a[m-1]:=a[m-1], a[lo];
  return m-1;
}

method Main(){
  var a:=new int[][4,7,3,4,6,1,9,78, -10, 0,-10];
  QuickSort(a);
  print a[..],"\n";
}