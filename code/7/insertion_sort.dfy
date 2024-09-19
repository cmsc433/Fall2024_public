predicate sorted(a: array<int>, l: int, u: int)
  reads a
  requires 0 <=l <=u <= a.Length
{
  forall i, j :: l <= i < j < u  ==> a[i] <= a[j]
}

/**
[3, 10, 8, 2, 7] → 
[3, 8, 10, 2, 7] →
[3, 8, 2, 10, 7] → 
[3, 2, 8, 10, 7] →
[2, 3, 8, 10, 7] →
[2, 3, 8, 7, 10]

For this algorith, in each step of the shuffle the new array is the permutation of the old array. 
Therefore, multiset(a[..]) == multiset(old(a[..])) holds during the shuffle. 

 */
method insertion_sort_shuffle(a: array<int>)
  modifies a
  requires a.Length >= 2
  ensures sorted(a, 0,a.Length)
  ensures multiset(a[..]) == multiset(old(a[..]))
{
  var i:= 1;
  while i < a.Length
    invariant 1 <= i <= a.Length
    invariant sorted(a, 0, i)
    invariant multiset(a[..]) == multiset(old(a[..]))
  {
    var j := i;
    while j >= 1 && a[j-1] > a[j]
      invariant 0 <= j <= i
      invariant forall k,l:: 0 <= k < l <= i && j != l ==> a[k] <= a[l]
      invariant multiset(a[..]) == multiset(old(a[..]))
    {
      a[j-1], a[j] := a[j], a[j-1];
      j := j - 1;
    }
    i := i + 1;
  }
}

/**

Let us insert item 2 into the correct position. 
[3, 8, 10, 2, 7] →
key = 2 //remember the current item
[3, 8, 10, 10, 7] → //move everything that is greater than key
[3, 8, 8, 10, 7] →
[3, 3, 8, 10, 7] →
now, swap key 2 with the current position
[2, 3, 8, 10, 7] 

For this algorith, during the shuffle, the new array is NOT the permutation 
of the old array. Therefore, 

multiset(a[..]) == multiset(old(a[..]))  // does not hold, but 

multiset(a[..][j:=key]) == multiset(old(a[..]))  // holds. 

*/

method insertion_sort_swap(a: array<int>)
  modifies a
  ensures sorted(a,0,a.Length)
  requires 0 < a.Length
  ensures multiset(a[..])==multiset(old(a[..]) )
  //requires forall k::0 <=k < a.Length ==> 1< a[k]< 15
{
  var i := 1;
  while i < a.Length
    invariant 1 <= i <= a.Length
    invariant sorted(a,0,i)
    invariant multiset(a[..]) == multiset(old(a[..]))
  {
    var key := a[i];
    var j := i;
    while j > 0 && a[j-1] > key
      invariant sorted(a,0,i)
      invariant forall k :: j <= k <= i ==> key <= a[k]
      invariant i == j || sorted(a,0,i+1)
      invariant multiset(a[..][j:=key]) == multiset(old(a[..]))
    {
      a[j] := a[j-1];
      j := j - 1;
    }
    assert sorted(a,0,i+1);
    a[j] := key;
    i := i + 1;
  }
}

method Main() {
  var a := new int[5][9, 14, 6, 3, 8];
  insertion_sort_swap(a);
  var k := 0;
  while(k < a.Length) { print a[k], ","; k := k+1;}
  print "\n";

  var b:=new int[][1,4,8,3,2];
  insertion_sort_shuffle(b);
  print (a[..]),"\n";

  var c:=new int[][1,2,3,4,5];
  var d:=multiset(c[..][2:=10]); // replace 3 with 10
  print (d),"\n";
}