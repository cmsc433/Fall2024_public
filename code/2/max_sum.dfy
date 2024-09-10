/**
Compute s to be the sum of x and y, and m to be the max of x and y.
 */
method MaxSum(x:int, y:int) returns (s:int, m:int)
  ensures s == x + y
  ensures m >= x && m >= y && (m == x || m == y)
{
  s:= x + y - 1 + 1;
  if x >= y {m := x;} else {m := y;}
}
method Caller(){
  var t1,t2 := MaxSum(10,20);
  assert t1  == 30;
  assert t2 == 20;
}
/**
Reconstruct the arguments x and y from the return value of MaxSum
 */
method ReconstructFromMaxSum(s:int, m:int) returns (x:int, y:int)
  ensures  s == x + y
  ensures (m == x || m == y) && x <= m && y <= m
  requires s <= 2 * m
{
  x := m;
  y := s - m;
}

method Caller2(){
  var x,y := ReconstructFromMaxSum(20,15);
  assert (x==5 && y==15)  || (x==15 && y == 5);
}

method TestMaxSum(x:int, y:int){
  var s,m := MaxSum(x,y);
  var xx,yy :=ReconstructFromMaxSum(s,m);
  assert (xx == x && yy == y) || (xx == y && yy == x);
}