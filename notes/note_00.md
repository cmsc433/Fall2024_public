
Dafny
-----

Dafny is a verification-aware programming language that has native support for recording specifications and is equipped with a static program verifier. It translates to Boogie, the backend, which interacts with Z3, a SMT solver.

Dafny is an imperative and functional compiled language that compiles to other programming languages, such as C#, Java, JavaScript, Go and Python. a Dafny program (stored as a file with extension .dfy) is a set of declarations. Here is a "hello world" program in Dafny.
```
method Main() {
  assert 1 == 1;
  print "hello, world\n";
}
```

Dafny can prove your code is correct, meaning it can:

*   Guarantee array indices stay in bounds
*   Guarantee no null dereferences
*   Guarantee no division by zero
*   Guarantee the program conforms to a specification

### Types

Dafny has various inbuild types:

*   `bool` for booleans
*   `char` for characters
*   `real`, `int`, `nat` for real, unbounded and natural numbers
*   `set<T>`, `seq<T>` for immutable finite sets
*   `array<T>` for arrays
*   `seq<T>` for representing an immutable ordered list, queues, stacks, etc. 
* `multiset<T>` Multisets are like sets in almost every way, except that they keep track of how many copies of each element they have. 
*   `object` is a super-type of all reference types

### Methods

Methods in Dafny are like functions or procedures in conventional languages. Input parameters and output arguments are typed as follows:
```
method Add(x: int, y: int) returns (sum: int)
{
  sum := x + y;
}
``` 

Input parameters are immutable. The output parameter is mutable and works like a local variable. A `return` statement is not necessary in a method, but if there is one, it need not have arguments or it must have all the return arguments of the method.
```
method Add(x: int, y: int) returns (sum: int)
{
  var s := x + y;
  return s;
}
```

```
method Add(x: int, y: int) returns (sum: int)
{
  var s := x + y;
  sum := s;
  return;
}
```
Here is another example:
```
method Abs(x: int) returns (y: int)
{
  if x < 0 {
    return -x;
  } else {
    return x;
  }
}
```

### Functions

Functions in Dafny side effect free and consist of a single expression that yields a value of some type.
```
function double(a:int): int
{
  a * 2
}
```    
If a function is declared a `ghost function`, it is only used for verification. 
```
ghost function abs(a:int): int
{
  if a > 0 then a else -a
}
``` 

### Predicates

A predicate is used for verification only. It is a special type of function in that it returns a `bool` only.
```
predicate Even( x : int ) { x % 2 == 0 }
``` 

#### `Main()`

The main method takes no input parameters and is the entry point of the program.

### Constructs

*   `if ... { ... } else { ... }` for conditionals
*   `//` or `/* ... */` for comments
*   `:=` for assignment
*   `==`, `<=`, `>=`, `!=`, `<`, `>` for boolean operations

### Pre- and Postconditions

The real power of Dafny comes from the ability to annotate these methods to specify their behavior. For example, one property that we observe with the Abs method is that the result is always greater than or equal to zero, regardless of the input. We could put this observation in a comment, but then we would have no way to know whether the method actually had this property. Further, if someone came along and changed the method, we wouldn’t be guaranteed that the comment was changed to match. With annotations, we can have Dafny prove that the property we claim of the method is true. There are several ways to give annotations, but some of the most common, and most basic, are method pre- and postconditions.

This property of the Abs method, that the result is always non-negative, is an example of a postcondition: it is something that is true after the method returns. Postconditions, declared with the `ensures` keyword, are given as part of the method’s declaration, after the return values (if present) and before the method body. The keyword is followed by the boolean expression. Like an if or while condition and most specifications, a postcondition is always a boolean expression: something that can be true or false. In the case of the Abs method, a reasonable postcondition is the following:
```
method Abs(x: int) returns (y: int)
  ensures 0 <= y
{
  if x < 0 {
    return -x;
  } else {
    return x;
  }
}
```
We can have multiple postconditions:
```
method MultipleReturns(x: int, y: int) returns (more: int, less: int)
  ensures less < x
  ensures x < more
{
  more := x + y;
  less := x - y;
}
```
The postcondition can also be written:
```
method MultipleReturns(x: int, y: int) returns (more: int, less: int)
  ensures less < x && x < more
{
  more := x + y;
  less := x - y;
}
```
or even:
```
method MultipleReturns(x: int, y: int) returns (more: int, less: int)
  ensures less < x < more
{
  more := x + y;
  less := x - y;
}
```
Preconditions have their own keyword, requires. We can give the necessary precondition to MultipleReturns as below:
```
method MultipleReturns(x: int, y: int) returns (more: int, less: int)
  requires 0 < y
  ensures less < x < more
{
  more := x + y;
  less := x - y;
}
```

### Assertions

Unlike pre- and postconditions, an assertion is placed somewhere in the middle of a method. Like the previous two annotations, an assertion has a keyword, assert, followed by the boolean expression and the semicolon that terminates simple statements. An assertion says that a particular expression always holds when control reaches that part of the code. For example, the following is a trivial use of an assertion inside a dummy method:
```
method Testing()
{
  assert 2 < 3;
  // Try "asserting" something that is not true.
  // What does Dafny output?
}
```
Another example:
```
method Square(x: int) returns (y: int)
  requires x >= 0
  ensures y == x*x
  {
    y := x*x;
    assert y > x;
  }
```    


### Compiling Dafny to Java
Let us comoile a simple Dafny program to Java and run the compiled Java code. 

The following dafny code `min.dfy` calculates the minimum of two integers. 
```java
function Minimum (x : int, y : int):(m : int)
ensures m <= x && m <= y
ensures m == x || m == y
{
    if x <= y then x else y
}

method Min (x : int, y : int) returns (m : int)
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

method Main ()
{
    var x := Min(2,1);
    print "Minimum is ", x;
}
```

Now, we can compile `min.dfy` to Java:
```
dafny build -t:java min.dfy
```
We can also run the Java code:
```
java -jar min.jar
Minimum is 1% 
```

Now, let us look at the generated Java code. First, we decompile the JAR. (For this example, I used https://www.decompiler.com/jar to decompile.)

```java
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
```

We can see that Dafny to Java compiler generated human readable Java code. Please read the instruction at https://dafny.org/dafny/Installation to comoile Dafny code to other languages, such as C#, Go, Python, and JavaScript. 
