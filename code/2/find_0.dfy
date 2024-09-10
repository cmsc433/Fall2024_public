method FindZero(a: array<int>) returns (index: int)
ensures index < 0 ==> forall i :: 0 <= i < a.Length ==> a[i] != 0
ensures 0 <= index ==> index < a.Length && a[index] == 0
{
    index := 0;
    while index < a.Length
    invariant forall k :: 0 <= k < index && k < a.Length ==> a[k] != 0
    {
        if a[index] == 0 {
            return;
        }
        index := index + 1;
    }
    index := -1;
}

method Main() {
  var a: array<int> := new int[5][9, 14, 6, 0, 8];
  var r :=FindZero(a);
  print "Found a zero at index ", r,"\n";
}