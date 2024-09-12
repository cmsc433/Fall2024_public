method test1(a:int, b:int) returns (r:int)
  ensures r == 1
{
  var x := a;
  assume{:axiom} x == 0;
  x :=x+1;
  assert x == 1;
  return x;

}
method test2(a:int, b:int)

{
  var i,j:= a,b;
  assume{:axiom} i > j;
  assert i > j;
  i :=i+1;
  assert i > j +1;
  j := j + 1;
  assert i > j;

}
method test3(a:int){
  var x := a;
  assume{:axiom} x== 2;
  assert x==2 ==> x > 1;
  assert x > 1;
  assert x +1 > 0;
  x := x +1;
  assert x > 0;
}


// {false} x:=x+1; {x > 100} valid
// {true} while true x:= x+1; {false} valid
method test4(a:int, b:int, c:int){
  var x,y,z:=a,b,c;
  //assume{:axiom} z == y + 1;
  assume{:axiom} z == 2;
  assert z * 2 == 4;
  x := z * 2 ;
  assert x == 4;
}

method test5(a:int, b:int)
  requires a + 1 <= b
{
  var x:=a;
  var n := b;
  // assume x+1 <= n;
  assert x +1 <= n; // P
  x := x+ 1;  //S
  assert x <= n; // Q
}

method test6(a:int, b:int){
  var x,y:=a,b;
  assume 2 * (x+3) >= 6;
  assert 2 * x >= 0;
  assert x >= 0;
  x := x + 3;
  assert 2 * x >= 6;
  x := 2 * x;
  assert x >= 6;
}

method test7(a:int, b:int){
  var x,y := a,b;
  assert true; // P
  if x <= 0

  { assert x <= 0;
    y := 2;
    assert x <= 0 && y ==2;
  }
  else
  { assert x > 0;
    y := x + 1;
    assert x > 0 && y == x + 1;
  }
  assert x <= 0 ==> y ==2 ==> x < y;
  assert x > 0 ==> y == x + 1 ==> x < y;
  //assert (x <= 0 && y ==2) ||  (x > 0 && y == x + 1);
  assert  x < y;
}

method test8(a:int, b:int){
  var x , y := a,b;

  assume x==y;
  //assert y == y;
  //assert y * 2 == y * 2;
  x := y * 2;
  assert x == 2 * y;
}

method test9(a:int, b:int){
  var x,y:=a,b;
  assume{:axiom} x > 0;
  if (x > 0)
  {y := x;}
  else
  {y := 0;}
  assert  y > 0;
}