// An annotated d Dafny program

method QuotDiv (m : int, n : int) returns (x : int, y : int)
  requires n > 0
  ensures n > x
  ensures y * n + x == m
{
  assert true ==> m == m;
  x := m;
  assert x == m;
  y := 0;
  assert y * n  + x  == m;
  while n <= x
    invariant y * n  + x  == m
  {
    assert y * n  + x  == m && n <= x ==> (y+1) * n + (x-n) == m;
    x := x - n;
    assert (y+1) * n + x == m;
    y := y + 1;
    assert y * n + x == m;
  }
  assert !(n <= x) && y * n + x == m ==>
      y * n + x == m && n > x;
}