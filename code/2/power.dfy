function pow(base: int, exp: nat): int {
 if exp == 0 then 1 else base * pow(base, exp-1)
}

method Power(base: int, exp:nat) returns (r: int)
ensures r == pow(base,exp)
{
  r := 1;
  var i: nat := 0;
  while i < exp
  invariant i <= exp
  invariant r == pow(base,i)
  {
   r := r * base;
   i := i + 1;
   assert r == pow(base,i);
  }
  assert i == exp;

}

method Main() {
  var a := [10,20,30];
  var s := Power (3,3);
  print s, ",";
}