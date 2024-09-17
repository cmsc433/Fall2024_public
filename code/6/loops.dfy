method test1(a:int, b:int, c:int){
  var x,y,z:=a,b,c;

  assume{:axiom}  y * (x+1) == 2 * z;
  assert y * (x + 1) == 2 * z;
  x := x + 1;

  assert y * x == 2 * z;
  y := y * x;
  assert y == 2 * z;

}

method test2(a:int, b:int){
  var x,y := a,b;

  assume{:axiom} x > 0;
  if (x > 0)
  {
    assert x > 0;
    y := x;
    assert x > 0 && y == x;
  }
  else
  {
    assert ! (x > 0);
    y := 0;
    assert (x <= 0) && y == 0;
  }

  //assert x > 0 ==> y == x && x <= 0 ==> y == 0;
  assert (x > 0 && x > 0 && y == x) ||  (x > 0 && x <= 0 && y == 0);
  assert y > 0;
}

method loop_to_0(a:int){
  var n := a;
  assume{:axiom}{:axiom} n > 0;
  var i := n;
  assert i <= n;
  while (i > 0)
    invariant i <= n
  {
    i := i - 1;
  }
  assert i == 0;
  assert i <= n;
  //assert i <= n  && (!(i < n));
  //       P           !b
}

method sum(n:nat) returns (s:nat)
  ensures s == n * (n+1)/2
{
  var j := 0;
  s := 0;
  assert s == j * (j+1)/2;
  while (j < n)
    invariant j <= n
    invariant s == j * (j+1)/2
  {
    //j 0 1 2 3
    //s 0 1 3 6
    j := j + 1;
    s := s + j;
  }
  //assert s == j * (j+1)/2;
  assert j == n;
  assert s == n * (n+1)/2;
}


function pow(base:int, exp:int):int
  requires exp >= 0
{
  if exp ==0 then 1 else base * pow(base, exp-1)
}

method pow2(base:int, exp:int) returns (r:int)
  requires exp >= 0
  ensures r == pow(base,exp)
{
  r := 1;
  var i := 0;
  assert r == pow(base, i);
  while i < exp
    invariant r == pow(base, i)
    invariant i <= exp
  {
    assert r == pow(base, i);
    r := r * base;
    i := i + 1;
  }
  assert i == exp;
  assert r == pow(base, i);
}


function swap<T>(a:T, b:T):(T,T){ 
  (b,a)
}

method swap2(a:int, b:int) returns (x:int, y:int){
  x,y := a,b;

  assert x ==a && y == b;
  assert  y == b && x  == a;

  x := x + y;
  assert x - (x - y) == b && x - y == a;
  y := x - y;
  assert x - y == b && y == a;
  x := x - y;
  assert x == b && y == a;

}

method swap3(a:int, b:int) returns (x:int, y:int){
  x,y := a,b;
  assert y == b && x == a;
  var tmp:= x;
  assert y == b && tmp == a;
  x := y;
  assert x == b && tmp == a;
  y := tmp;
  assert x == b && y == a;

}
method swap4(a:bv16, b:bv16) returns (x:bv16, y:bv16){
  x,y:=a,b;
  assert x == a && y == b;
  assert y == b &&  x  == a;
  x := x ^ y;
  assert x ^  x ^ y == b &&  x ^ y == a;
  y := x ^ y;
  assert x ^ y == b && y == a;
  x := x ^ y;
  assert x == b && y == a;

}

method Main(){
  var r := pow2(3,3);
  print r;
}