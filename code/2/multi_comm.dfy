function Mult(x:nat, y:nat):nat
{
  if y == 0 then 0 else x + Mult(x, y-1)
}

/**

Prove multiplication is commutative
 */
lemma MultiComm (x:nat, y:nat)
  ensures Mult(x,y) == Mult(y,x)
{
  if x == y {
  }else if x == 0 {
    MultiComm(x, y-1);
  }else if y == 0 {
    MultiComm(x-1, y);
  }else
  {
    MultiComm(x-1, y-1);
  }
}

/**

Prove multiplication is commutative without Dafny's automatic induction
 */
lemma {:induction false} MultiComm' (x:nat, y:nat)
  ensures Mult(x,y) == Mult(y,x)
{
  if x == y {
  }else if x == 0 {
    MultiComm'(x, y-1);
  }else if y == 0 {
    MultiComm'(x-1, y);
  }else
  {
    calc{
      Mult(x,y);
    ==
      x + Mult(x, y-1);
    ==
       {MultiComm'(x, y-1);}
      x + Mult(y-1, x);
    ==
      x + y - 1 + Mult(y-1, x-1);
    == {MultiComm'(x-1, y-1);}
      x + y - 1 + Mult(x-1, y-1);
    ==
      y + Mult(x-1, y);
    == {MultiComm'(x-1, y);}
      y + Mult(y,x-1);
    ==
      Mult(y,x);
    }
  }
}