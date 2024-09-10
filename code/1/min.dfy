function Minimum (x : int, y : int):(m : int)
//requires x > 0
ensures m <= x && m <= y
ensures m == x || m == y
{
    if x <= y then x else y
}
method test1(){
   assert 10 == Minimum(20,10);
}

method Min (x : int, y : int) returns (m : int)
//requires x > 0
ensures m == Minimum(x,y)
{
    if (x < y) {
        m := x;  // Could also use "return x"
    }
    else {
        m := y;
        // return y;  // Could also use " m := y"
    }
}
method test2(){
   var x:= Min(20,10);
   assert 10 == x;
}

method Main ()
{
    var x := Min(2,1);
    print "Minimum is ", x;
}

/*

Compile the Dafny to Java:

dafny build -t:java min.dfy

Run the Java code:

java -jar min.jar

Decompile the JAR on https://www.decompiler.com/jar

Here is the decompiled Java code:

package _System;

import dafny.CodePoint;
import dafny.DafnySequence;
import java.math.BigInteger;

public class __default {
   public static BigInteger Minimum(BigInteger var0, BigInteger var1) {
      return var0.compareTo(var1) <= 0 ? var0 : var1;
   }

   public static BigInteger Min(BigInteger var0, BigInteger var1) {
      BigInteger var2 = BigInteger.ZERO;
      if (var0.compareTo(var1) < 0) {
         var2 = var0;
      } else {
         var2 = var1;
      }

      return var2;
   }

   public static void Main(DafnySequence<? extends DafnySequence<? extends CodePoint>> var0) {
      BigInteger var1 = BigInteger.ZERO;
      BigInteger var2 = BigInteger.ZERO;
      var2 = Min(BigInteger.valueOf(2L), BigInteger.ONE);
      System.out.print(DafnySequence.asUnicodeString("Minimum is ").verbatimString());
      System.out.print(String.valueOf(var2));
   }

   public static void __Main(DafnySequence<? extends DafnySequence<? extends CodePoint>> var0) {
      Main(var0);
   }

   public String toString() {
      return "_module._default";
   }
}
*/