/** Hoare Triples and Dafny */

/** A _Hoare triple_ is a claim about the state before and
    after executing a statement.  The standard notation is

      {P} s {Q}

    meaning:

      - If statement s begins execution in a state satisfying assertion P,
      - and if s eventually terminates in some final state,
      - then that final state will satisfy the assertion Q.

    Assertion P is called the _precondition_ of the triple, and Q is
    the _postcondition_.

    For example,

    - {x == 0} x := x + 1 {x == 1} is a valid Hoare triple,
      stating that the statement x := x + 1 would transform a state in
      which x == 0 to a state in which x == 1.

    - forall m, {x == m} x := x + 1 {x == m + 1}, is a
      _proposition_ stating that the Hoare triple {x == m} x := x +
      m {x == m + 1} is valid for any choice of m.  Note that m
      in the two assertions and the command in the middle is a
      reference to the _Dafny_ variable m, which is bound outside the
      Hoare triple. */

/* ################################################################# */
/** * Proof Rules 

    The goal of Hoare logic is to provide a _compositional_
    method for proving the validity of specific Hoare triples.  That
    is, we want the structure of a program's correctness proof to
    mirror the structure of the program itself.  To this end, in the
    sections below, we'll introduce a rule for reasoning about each of
    the different syntactic forms of statements in Dafny -- one for
    assignment, one for sequencing, one for conditionals, etc. -- plus
    a couple of "structural" rules for gluing things together.  We
    will then be able to prove programs correct using these proof
    rules. */

/* ================================================================= */
/** ** Empty statement blocks 

    Since empty statement blocks don't change the state, they preserve any
    assertion P:

      ---------------------  (hoare_skip)
         { P } {} { P }
*/

/* ================================================================= */
/** ** Sequencing 

    If statement s1 takes any state where P holds to a state where
    Q holds, and if s2 takes any state where Q holds to one
    where R holds, then doing s1 followed by s2 will take any
    state where P holds to one where R holds:

           { P } s1 { Q }
           { Q } s2 { R }
       ----------------------  (hoare_seq)
         { P } s1; s2 { R }
*/

/* ================================================================= */
/** ** Assignment 

    The rule for assignment is the most fundamental of the Hoare
    logic proof rules.  Here's how it works.

    Consider this incomplete Hoare triple:

       { ??? }  x := y  { x == 1 }

    We want to assign y to x and finish in a state where x is 1.
    What could the precondition be?

    One possibility is y == 1, because if y is already 1 then
    assigning it to x causes x to be 1.  That leads to a valid
    Hoare triple:

       { y == 1 }  x := y  { x == 1 }

    It may seem as though coming up with that precondition must have
    taken some clever thought.  But there is a mechanical way we could
    have done it: if we take the postcondition x == 1 and in it
    replace x with y---that is, replace the left-hand side of the
    assignment statement with the right-hand side---we get the
    precondition, y == 1. 

    That same idea works in more complicated cases.  For
    example:

       { ??? }  x := x + y  { x == 1 }

    If we replace the x in x == 1 with x + y, we get x + y == 1.
    That again leads to a valid Hoare triple:

       { x + y == 1 }  x := x + y  { x == 1 }

    Why does this technique work?  The postcondition identifies some
    property P that we want to hold of the variable x being
    assigned.  In this case, P is "equals 1".  To complete the
    triple and make it valid, we need to identify a precondition that
    guarantees that property will hold of x.  Such a precondition
    must ensure that the same property holds of _whatever is being
    assigned to_ x.  So, in the example, we need "equals 1" to
    hold of x + y.  That's exactly what the technique guarantees. 

    In general, the postcondition could be some arbitrary assertion
    Q, and the right-hand side of the assignment could be some
    arbitrary arithmetic expression a:

       { ??? }  x := a  { Q }

    The precondition would then be Q, but with any occurrences of
    x in it replaced by a.

    Let's introduce a notation for this idea of replacing occurrences:
    Define Q[x := a] to mean "Q where a is substituted in
    place of x".

    This yields the Hoare logic rule for assignment:

      ---------------------------- (hoare_asgn)
      { Q[x := a] }  x := a  { Q }

    One way of reading this rule is: If you want statement x := a
    to terminate in a state that satisfies assertion Q, then it
    suffices to start in a state that also satisfies Q, except
    where a is substituted for every occurrence of x. 

    To many people, this rule seems "backwards" at first, because
    it proceeds from the postcondition to the precondition.  Actually
    it makes good sense to go in this direction: the postcondition is
    often what is more important, because it characterizes what we
    can assume afer running the code.
*/

/** Here are some valid instances of the assignment rule:

      { x + 1 <= 5 } 
        x := x + 1
      { x <= 5 }

      { (x == 3) [x := 3] }        (that is, 3 = 3)
        x := 3
      { x = 3 }


*/

/* ================================================================= */
/** ** Consequence 

    Sometimes the preconditions and postconditions we get from the
    Hoare rules won't quite be the ones we want in the particular
    situation at hand -- they may be logically equivalent but have a
    different syntactic form that fails to unify with the goal we are
    trying to prove, or they actually may be logically weaker (for
    preconditions) or stronger (for postconditions) than what we need. 

    For instance,

      {3 == 3} x := 3 {x == 3},

    follows directly from the assignment rule, but

      {true} x := 3 {x == 3}

    does not.  This triple is valid, but it is not an instance of
    [hoare_asgn] because true and (x == 3) [x := 3] are not
    syntactically equal assertions.

    However, they are logically _equivalent_, so if one triple is
    valid, then the other must certainly be as well.  We can capture
    this observation with the following rule:

                {P'} s {Q}
                  P <-> P'
         -------------------------   (hoare_consequence_pre_equiv)
                 {P} s {Q}


    Taking this line of thought a bit further, we can see that
    strengthening the precondition or weakening the postcondition of a
    valid triple always produces another valid triple. This
    observation is captured by two _Rules of Consequence_.

                {P'} c {Q}
                  P -> P'
         -----------------------------   (hoare_consequence_pre)
                {P} s {Q}

                {P} s {Q'}
                 Q' -> Q
         -----------------------------    (hoare_consequence_post)
                {P} s {Q}
*/

/* ================================================================= */
/** ** Conditionals 

    What sort of rule do we want for reasoning about conditional
    statements?

    Certainly, if the same assertion Q holds after executing
    either of the branches, then it holds after the whole conditional.
    So we might be tempted to write:

             
         {P} s1 {Q}      {P} s2 {Q}
      ---------------------------------
       {P} if b { s1 } else { s2 } {Q}

    However, this is rather weak. For example, using this rule,
    we cannot show
   
      { true }
        if x <= 0
          { y := 2 }
        else 
          { y := x + 1 }
      { x <= y }
   
    since the rule tells us nothing about the state in which the
    assignments take place in the "then" and "else" branches.

    Fortunately, we can say something more precise.  In the
    "then" branch, we know that the boolean expression b evaluates to
    true, and in the "else" branch, we know it evaluates to false.
    Making this information available in the premises of the rule gives
    us more information to work with when reasoning about the behavior
    of s1 and s2 (i.e., the reasons why they establish the
    postcondition Q).

                
         {P &&  b} s1 {Q}  {P && !b} s2 {Q}
      ----------------------------------------  (hoare_if)
           {P} if b { s1 } else { s2 } {Q}
*/

/* In class: 

What would a hoare rule for 1-sided conditionals look like?
Fill in the following rule.

  {P && b} s1 {Q}    P && !b -> Q
---------------------------------- (hoare_if1)
       {P} if b {s1} {Q}
*/


/* ================================================================= */
/** ** While Loops 

    The Hoare rule for while loops is based on the idea of an
    _invariant_: an assertion whose truth is guaranteed before and
    after executing a statement.  An assertion P is an invariant of s if

      {P} s {P}

    holds.  Note that in the middle of executing s, the invariant
    might temporarily become false, but by the end of s, it must be
    restored. 

    As a first attempt at a [while] rule, we could try:

            {P} s {P}
      ---------------------
      {P} while b { s } {P}

    That rule is valid: if P is an invariant of s, as the premise
    requires, then no matter how many times the loop body executes,
    s is going to be true when the loop finally finishes.

    But the rule also omits two crucial pieces of information.  First,
    the loop terminates when b becomes false.  So we can strengthen
    the postcondition in the conclusion:

              {P} s {P}
      ---------------------------
      {P} while b { s } {P && !b}

    Second, the loop body will be executed only if [b] is true.  So we
    can also strengthen the precondition in the premise:

            {P && b} s {P}
      --------------------------- (hoare_while)
      {P} while b { s } {P && !b}

    That is the Hoare [while] rule.  Note how it combines
    aspects of empty blocks and conditionals:

    - If the loop body executes zero times, the rule is like an empty block in
      that the precondition survives to become (part of) the postcondition.

    - Like a conditional, we can assume guard b holds on entry to
      the substatement     
*/

/* ################################################################# */
/** * Decorated Programs */

/** The beauty of Hoare Logic is that it is _structure-guided_: the
    structure of proofs exactly follows the structure of programs.

    We can record the essential ideas of a Hoare-logic proof --
    omitting low-level calculational details -- by "decorating" a
    program with appropriate assertions on each of its commands.

    Such a _decorated program_ carries within itself an argument for
    its own correctness. 

    For example, consider the program: 
 */

method LoopToZero_1(m : int, p : int) returns (x: int, z: int) {
  x := m;
  z := p;
  while x > 0 {
    z := z - 1;
    x := x - 1;
  }
}

/* 
    Here is one possible specification for this program, in the
    form of a Hoare triple:

    { true }
    x := m;
    z := p;
    while x > 0 {
      z := z - 1;
      x := x - 1;
    }
    { z == p - m }

    and here is the equivalent specification in terms of 
    Dafny's _requires_ and _ensures_ syntax (of course,
    Dafny can't prove this without an invariant annotation):
*/
method LoopToZero_2(m : nat, p : int) returns (x: nat, z: int)
  requires true
  ensures z == p - m
{
  x := m;
  z := p;
  while x > 0
    invariant (z - x == p - m)
  {
    z := z - 1;
    x := x - 1;
  }
}

/** Here is a decorated version of this program, embodying a
    proof of this specification:
*/

method LoopToZero_3(m : nat, p : int) returns (x: nat, z: int) {
  //  { true } ->
  //  { m == m }
  x := m;
  //  { x == m } ->
  //  { x == m && p == p };
  z := p;
  //  { x == m && z == p } ->
  //  { z - x == p - m }
  while x > 0 {
    //      { z - x == p - m && x > 0 } ->
    //      { (z - 1) - (x - 1) == p - m }
    z := z - 1;
    //      { z - (x - 1) == p - m }
    x := x - 1;
    //      { z - x == p - m }
  }
  //  { z - x == p - m && !(x > 0) } ->
  //  { z == p - m }
}

/** That is, a decorated program consists of the program's text
    interleaved with assertions (sometimes multiple assertions
    separated by implications). 

    A decorated program can be viewed as a compact representation of a
    proof in Hoare Logic: the assertions surrounding each command
    specify the Hoare triple to be proved for that part of the program
    using one of the Hoare Logic rules, and the structure of the
    program itself shows how to assemble all these individual steps
    into a proof for the whole program. 

    Dafny's goal is to verify such decorated programs "mostly
    automatically."  But, before we can verify anything, we need to be
    able to _find_ a proof for a given specification, and for this we
    need to discover the right assertions. This can be done in an
    almost mechanical way, with the exception of finding loop
    invariants. We'll first explain in detail how to construct 
    decorations for several short programs, all of which are 
    loop-free or have simple loop invariants. We'll return
    to finding more interesting loop invariants later. 
*/

/* ================================================================= */
/** ** Example: Swapping 

    Consider the following program, which swaps the values of two
    variables using addition and subtraction (instead of by assigning
    to a temporary variable).

       x := x + y;
       y := x - y;
       x := x - y

    We can give a proof, in the form of decorations, that this program is
    correct -- i.e., it really swaps x and y -- as follows.

    (1)    { x == m && y == n } ->
    (2)    { (x + y) - ((x + y) - y) == n && (x + y) - y == m }
             x := x + y;
    (3)    { x - (x - y) == n && x - y == m }
             y := x - y;
    (4)    { x - y == n && y == m }
             x := x - y
    (5)    { x == n && y == m }

    The decorations can be constructed as follows:

      - We begin with the undecorated program (the unnumbered lines).

      - We add the specification -- i.e., the outer precondition (1)
        and postcondition (5). In the precondition, we use parameters
        m and n to remember the initial values of variables x
        and y so that we can refer to them in the postcondition (5).

      - We work backwards, mechanically, starting from (5) and
        proceeding until we get to (2). At each step, we obtain the
        precondition of the assignment from its postcondition by
        substituting the assigned variable with the right-hand-side of
        the assignment. For instance, we obtain (4) by substituting
        x with x - y in (5), and we obtain (3) by substituting y
        with x - y in (4).

    Finally, we verify that (1) logically implies (2) -- i.e., that
    the step from (1) to (2) is a valid use of the law of
    consequence -- by doing a bit of high-school algebra.
*/

/* ================================================================= */
/** ** Example: Simple Conditionals 

    Here is a simple program using conditionals,
    assuming x, y, and z are natural numbers (as in: non-negative 
    integers):
*/

method simpleIf(x:nat, y:nat) returns (z:nat)
  ensures z + x == y || z + y == x
{
  if x <= y {
    z := y - x;
  } else {
    z := x - y;
  }
}

/*
    Here is a decorated version of the same program:

      (1)   { true }
              if x <= y {
      (2)      { true && x <= y } ->
      (3)      { (y - x) + x == y || (y - x) + y == x }
                 z := y - x
      (4)      { z + x == y || z + y == x }
              } else {
      (5)       { true && ~(x <= y) } ->
      (6)       { (x - y) + x == y || (x - y) + y = x }
                z := x - y
      (7)       { z + x = y || z + y = x }
              }
      (8)   { z + x = y || z + y = x }

These decorations can be constructed as follows:

  - We start with the outer precondition (1) and postcondition (8).

  - Following the format dictated by the [hoare_if] rule, we copy the
    postcondition (8) to (4) and (7). We conjoin the precondition (1)
    with the guard of the conditional to obtain (2). We conjoin (1)
    with the negated guard of the conditional to obtain (5).

  - In order to use the assignment rule and obtain (3), we substitute
    z by y - x in (4). To obtain (6) we substitute z by x - y
    in (7).

  - Finally, we verify that (2) implies (3) and (5) implies (6). Both
    of these implications crucially depend on the ordering of x and
    y obtained from the guard. For instance, knowing that x <= y
    ensures that subtracting x from y and then adding back x
    produces y, as required by the first disjunct of (3). Similarly,
    knowing that !(x <= y)] ensures that subtracting y from x
    and then adding back y produces x, as needed by the second
    disjunct of (6). Note that n - m + m = n does _not_ hold for
    arbitrary natural numbers n and m (Dafny, in particular, won't
    even let you perform a subtraction that would get you in the 
    negatives)
*/

/* ================================================================= */
/** ** Example: Reduce to Zero 

    Here is a while loop that is so simple that true suffices
    as a loop invariant when x is a nat - that is, Dafny doesn't 
    even need an invariant annotation to verify it (why?)

*/
method LoopToZero_Simple(n : nat) returns (x : nat)
  ensures x == 0
{
  x := n;
  while x > 0 
    invariant true
  {
    x := x - 1;
  }
}

/* Here is it's annotated version:

        (1)    {true}
                 while x > 0 {
        (2)       { true && x > 0 } ->
        (3)       { true }
                   x := x - 1
        (4)       { true }
                 }
        (5)    { true && !(x > 0) } ->
        (6)    { x = 0 }

   The decorations can be constructed as follows:

     - Start with the outer precondition (1) and postcondition (6).

     - Following the format dictated by the [hoare_while] rule, we copy
       (1) to (4). We conjoin (1) with the guard to obtain (2). We also
       conjoin (1) with the negation of the guard to obtain (5).

     - Because the final postcondition (6) does not syntactically match (5),
       we add an implication between them.

     - Using the assignment rule with assertion (4), we trivially substitute
       and obtain assertion (3).

     - We add the implication between (2) and (3).

   Finally we check that the implications do hold; both are trivial. */

/* ================================================================= */
/** ** Example: Division 

    Let's do one more example of simple reasoning about a loop.

    The following program calculates the integer quotient and
    remainder of parameters m and n. 
    (Dafny complains about the invariant and the loop's termination. 
    How would you fix the latter?)
*/
/*
method QuotDiv (m : int, n : int) returns (x : int, y : int) 
{
       x := m;
       y := 0;
       while n <= x
       {
         x := x - n;
         y := y + 1;
       }
}*/

/*  If we execute this program, it will terminate with the variable
    x set to the remainder when m is divided by n and y set to the 
    quotient. 

    In order to give a specification to this program we need to
    remember that dividing m by n produces a remainder x and a
    quotient y such that n * y + x == m && x < n].

    It turns out that we get lucky with this program and don't have to
    think very hard about the loop invariant: the invariant is just
    the first conjunct, [n * y + x == m], and we can use this to
    decorate the program.

      (1)  { true } ->
      (2)  { n * 0 + m == m }
             x := m;
      (3)  { n * 0 + x == m }
             y := 0;
      (4)  { n * y + x == m }
             while n <= x {
      (5)  { n * y + x == m && n <= x } ->
      (6)  { n * (y + 1) + (x - n) == m }
               x := x - n;
      (7)  { n * (y + 1) + x == m }
               y := y + 1;
      (8)  { n * y + x == m }
             }
      (9)  { n * y + x == m && !(n <= x) } -> 
     (10)  { n * y + x == m && x < n }

    Assertions (4), (5), (8), and (9) are derived mechanically from
    the invariant and the loop's guard.  Assertions (8), (7), and (6)
    are derived using the assignment rule going backwards from (8)
    to (6).  Assertions (4), (3), and (2) are again backwards
    applications of the assignment rule.

    Now that we've decorated the program it only remains to check that
    the uses of the consequence rule are correct -- i.e., that (1)
    implies (2), that (5) implies (6), and that (9) implies (10). This
    is indeed the case:
      - (1) -> (2):  trivial, by algebra.
      - (5) -> (6):  because [n <= x], we are guaranteed that the
        subtraction in (6) does not get zero-truncated.  We can
        therefore rewrite (6) as [n * y + n + x - n] and cancel the
        ns, which results in the left conjunct of (5).
      - (9) -> (10):  if [!(n <= x)] then [x < n].  That's straightforward
        from high-school algebra.

    So, we have a valid decorated program. 
    */

/* ################################################################# */
/** * Finding Loop Invariants 

    Once the outermost precondition and postcondition are
    chosen, the only creative part of a verifying program using Hoare
    Logic is finding the right loop invariants.  The reason this is
    difficult is the same as the reason that inductive mathematical
    proofs are:

    - Strengthening a _loop invariant_ means that you have a stronger
      assumption to work with when trying to establish the
      postcondition of the loop body, but it also means that the loop
      body's postcondition is stronger and thus harder to prove.

    - Strengthening an _induction hypothesis_ means that you have a
      stronger assumption to work with when trying to complete the
      induction step of the proof, but it also means that the
      statement being proved inductively is stronger and thus harder
      to prove.

    This section explains how to approach the challenge of finding
    loop invariants through a series of examples and exercises. */

/* ================================================================= */
/** ** Example: Slow Subtraction 

    The following program subtracts the value of x from the value of
    y by repeatedly decrementing both x and y.  We want to verify its
    correctness with respect to the pre- and post-conditions shown:
    
           { x == m && y == n }
             while !(x == 0) do
               y := y - 1;
               x := x - 1;
             end
           { y == n - m }

    To verify this program, we need to find an invariant [Inv] for the
    loop.  As a first step we can leave [Inv] as an unknown and build a
    _skeleton_ for the proof by applying the rules for local
    consistency, working from the end of the program to the beginning,
    as usual, and without any thinking at all yet. *)

(** This leads to the following skeleton:

        (1)    { x == m && y == n }  ->                   (a)
        (2)    { Inv }
                 while x > 0 {}
        (3)    { Inv && x > 0 }  ->                       (c)
        (4)    { Inv [x := x-1] [y := y-1] }
                   y := y - 1;
        (5)    { Inv [x := x-1] }
                   x := x - 1
        (6)    { Inv }
                 }
        (7)    { Inv && !(x > 0) }  ->                    (b)
        (8)    { y == n - m }

    By examining this skeleton, we can see that any valid [Inv] will
    have to respect three conditions:
    - (a) it must be _weak_ enough to be implied by the loop's
      precondition, i.e., (1) must imply (2);
    - (b) it must be _strong_ enough to imply the program's postcondition,
      i.e., (7) must imply (8);
    - (c) it must be _preserved_ by each iteration of the loop (given
      that the loop guard evaluates to true), i.e., (3) must imply (4). 

    These conditions are actually independent of the particular
    program and specification we are considering: every loop
    invariant has to satisfy them.

    One way to find an invariant that simultaneously satisfies these
    three conditions is by using an iterative process: start with a
    "candidate" invariant (e.g., a guess or a heuristic choice) and
    check the three conditions above; if any of the checks fails, try
    to use the information that we get from the failure to produce
    another -- hopefully better -- candidate invariant, and repeat.

    For instance, in the reduce-to-zero example above, we saw that,
    for a very simple loop, choosing [true] as an invariant did the
    job.  Maybe it will work here too.  To find out, let's try
    instantiating [Inv] with [true] in the skeleton above and
    see what we get...

        (1)    { x == m && y == n } ->                    (a - OK)
        (2)    { true }
                 while x > 0 {}
        (3)    { true && x > 0 } ->                       (c - OK)
        (4)    { true }
                   y := y - 1;
        (5)    { true }
                   x := x - 1
        (6)    { true }
                 }
        (7)    { true && !(x > 0) } ->                 (b - WRONG!)
        (8)    { y == n - m }

    While conditions (a) and (c) are trivially satisfied,
    (b) is wrong: it is not the case that [true && !(x > 0)] (7)
    implies [y == n - m] (8).  In fact, the two assertions are
    completely unrelated, so it is very easy to find a counterexample
    to the implication (say, [y = x = m = 0] and [n = 1]).

    If we want (b) to hold, we need to strengthen the invariant so
    that it implies the postcondition (8).  One simple way to do
    this is to let the invariant _be_ the postcondition.  So let's
    return to our skeleton, instantiate [Inv] with [y == n - m], and
    try checking conditions (a) to (c) again.

    (1)    { x == m && y == n } ->              (a - WRONG!)
    (2)    { y == n - m }
             while x > 0 do
    (3)    { y == n - m && x > 0 } ->           (c - WRONG!)
    (4)    { y - 1 == n - m }
               y := y - 1;
    (5)    { y == n - m }
               x := x - 1
    (6)    { y == n - m }
             }
    (7)    { y == n - m && !(x > 0) } ->            (b - OK)
    (8)    { y == n - m }

    This time, condition (b) holds trivially, but (a) and (c) are
    broken. Condition (a) requires that (1) [x == m && y == n]
    implies (2) [y == n - m].  If we substitute y by n we have to
    show that [n == n - m] for arbitrary m and n, which is not
    the case (for instance, when m = n = 1).  Condition (c) requires
    that [n - m - 1 == n - m], which fails, for instance, for n = 1
    and m = 0. So, although [y == n - m] holds at the end of the loop,
    it does not hold from the start, and it doesn't hold on each
    iteration; it is not a correct invariant.

    This failure is not very surprising: the variable y changes
    during the loop, while m and n are constant, so the assertion
    we chose didn't have much chance of being an invariant!

    To do better, we need to generalize (7) to some statement that is
    equivalent to (8) when x is 0, since this will be the case
    when the loop terminates, and that "fills the gap" in some
    appropriate way when x is nonzero.  Looking at how the loop
    works, we can observe that x and y are decremented together
    until x reaches 0.  So, if [x == 2] and [y == 5] initially,
    after one iteration of the loop we obtain [x == 1] and [y == 4];
    after two iterations [x == 0] and [y == 3]; and then the loop stops.
    Notice that the difference between y and x stays constant
    between iterations: initially, [y == n] and [x == m], and the
    difference is always (n - m).  So let's try instantiating [Inv] in
    the skeleton above with [y - x == n - m].

    (1)    { x == m && y == n } ->                            (a - OK)
    (2)    { y - x == n - m }
             while x > 0 {
    (3)    { y - x == n - m && x > 0 } ->                     (c - OK)
    (4)    { (y - 1) - (x - 1) == n - m }
               y := y - 1;
    (5)    { y - (x - 1) = n - m }
               x := x - 1
    (6)    { y - x == n - m }
             }
    (7)    { y - x == n - m && !(x > 0) } ->                (b - OK?)
    (8)    { y = n - m }

    Success? If everything is a natural number conditions (a), (b) 
    and (c) all hold now; However, the same is not true if everything 
    is an integer, as !(x > 0) does not imply x = 0! In that case, we would
    need to further strengthen the invariant to include that x >= 0 
    (assuming that's the case to begin with): 
    
    (1)    { m >= 0 && n >= 0 && x == m && y == n } ->                 (a - OK)
    (2)    { y - x == n - m }
             while x > 0 {
    (3)    { x >= 0 && y - x == n - m && x > 0 } ->                    (c - OK)
    (4)    { (x - 1) >= 0 && (y - 1) - (x - 1) == n - m }
               y := y - 1;
    (5)    { (x - 1) >= 0 && y - (x - 1) = n - m }
               x := x - 1
    (6)    { x >= 0 && y - x == n - m }
             }
    (7)    { x >= 0 && y - x == n - m && !(x > 0) } ->                (b - OK)
    (8)    { y = n - m }
*/

/* ================================================================= */
/** ** Exercise: Slow Assignment 

    A roundabout way of assigning a number currently stored in x to
    the variable y is to start y at 0, then decrement x until
    it hits 0, incrementing y at each step. Here is a program that
    implements this idea.  Fill in decorations.

(IN CLASS)
   { x == m } ->
                    { Inv [y := 0]} 
      y := 0;
                    { Inv } 
      while x > 0 {
                    { Inv && x > 0 } ->
                    { Inv [y := y+1][x := x-1] }
         x := x - 1;
                    { Inv [y := y+1] } 
         y := y + 1;
                    { Inv  }
      }
    { Inv && ! (x > 0) } ->
    { y == m }

Candidates:
Inv := x + y == m
   { x == m } -> { x + 0 == m } 
   { x + y == m && x > 0 } -> { (x-1) + (y+1) == m }
   { x + y == m && ! (x > 0) } -> { y == m }

Inv := x + y == m && x >= 0
   { x == m } -> { x + 0 == m && x >= 0 } 
   { x + y == m && x >= 0 && x > 0 } -> 
     { (x-1) + (y+1) == m && (x-1) >= 0 }
   { x + y == m && x >= 0 && ! (x > 0) } -> { y == m }
*/

/* ================================================================= */
/** ** Example: Parity 

    Here is a cute way of computing the parity of a value initially
    stored in x, due to Daniel Cristofani.

       { x == m }
         while 2 <= x do
           x := x - 2
         end
       { x = parity m }

    The parity function used in the specification is defined in
    as follows: 
*/
function parity(x:nat): nat {
  match x
  case 0 => 0
  case 1 => 1
  case _ => parity (x - 2)
}

method compute_parity(m:nat) returns (x:nat)
  // requires true 
  // ensures (x == parity(m))
{
  // { true } ->
  // { parity(m) == parity(m) }
  x := m;
  // { parity(x) == parity(m) }
  while 2 <= x
  {
    // {parity(x) == parity(m) && 2 <= x}
    // {parity(x - 2) == parity(m)}
    x := x - 2;
    // {parity(x) == parity(m)}
  }
  // { parity(x) == parity(m) && !(2 <= x)} ->
  // { x == parity(m) }
}

/** The postcondition does not hold at the beginning of the loop,
    since [m == parity m] does not hold for an arbitrary m, so we
    cannot hope to use that as an invariant.  To find an invariant that works,
    let's think a bit about what this loop does.  
    
    On each iteration it
    decrements x by 2, which preserves the parity of x.  So the
    parity of x does not change, i.e., it is invariant.  The initial
    value of x is m, so the parity of x is always equal to the
    parity of m. Using [parity x == parity m] as an invariant we
    obtain the following decorated program:

      { x == m } ->                                         (a - OK)
      { parity x == parity m }
        while 2 <= x do
                     { parity x == parity m && 2 <= x } ->   (c - OK)
                     { parity (x-2) == parity m }
          x := x - 2
                     { parity x == parity m }
        end
      { parity x == parity m && !(2 <= x) } ->               (b - OK)
      { x == parity m }

    With this invariant, conditions (a), (b), and (c) are all
    satisfied. For verifying (b), we observe that, when [x < 2], we
    have [parity x = x] (we can easily see this in the definition of
    [parity]).  For verifying (c), we observe that, when [2 <= x], we
    have [parity x = parity (x-2)]. 
*/

/* ================================================================= */
/** ** Example: Finding Square Roots 

    The following program computes the integer square root of x
    by naive iteration:

    { x == m }
      z := 0;
      while (z+1)*(z+1) <= x {
        z := z+1
      }
    { z*z<=m && m<(z+1)*(z+1) }


    As we did before, we can try to use the postcondition as a
    candidate invariant, obtaining the following decorated program:

    (1)  { x==m } ->                           (a - second conjunct of (2) WRONG!)
    (2)  { 0*0 <= m && m<(0+1)*(0+1) }
            z := 0
    (3)  { z*z <= m && m<(z+1)*(z+1) };
            while (z+1)*(z+1) <= x {
    (4)  { z*z<=m && m<(z+1)*(z+1) && (z+1)*(z+1)<=x } ->>            (c - WRONG!)
    (5)  { (z+1)*(z+1)<=m && m<((z+1)+1)*((z+1)+1) }
              z := z+1
    (6)  { z*z<=m && m<(z+1)*(z+1) }
            }
    (7)  { z*z<=m && m<(z+1)*(z+1) && !((z+1)*(z+1)<=x) } ->>  (b - OK)
    (8)  { z*z<=m && m<(z+1)*(z+1) }

    This didn't work very well: conditions (a) and (c) both failed.
    Looking at condition (c), we see that the second conjunct of (4)
    is almost the same as the first conjunct of (5), except that (4)
    mentions x while (5) mentions m. But note that x is never
    assigned in this program, so we should always have x=m. We
    didn't propagate this information from (1) into the loop
    invariant, but we could!

    Also, we don't need the second conjunct of (8), since we can
    obtain it from the negation of the guard -- the third conjunct
    in (7) -- again under the assumption that [x==m].  This allows
    us to simplify a bit.

    So we now try [x==m && z*z <= m] as the loop invariant:

    { x==m } ->                                           (a - OK)
    { x==m && 0*0 <= m }
      z := 0
                 { x==m && z*z <= m };
      while (z+1)*(z+1) <= x do
                 { x==m && z*z<=m && (z+1)*(z+1)<=x } ->  (c - OK)
                 { x==m && (z+1)*(z+1)<=m }
        z := z + 1
                 { x==m && z*z<=m }
      end
    { x=m && z*z<=m && ~((z+1)*(z+1)<=x) } ->             (b - OK)
    { z*z<=m && m<(z+1)*(z+1) }

    This works, since conditions (a), (b), and (c) are now all
    trivially satisfied.

    Very often, when a variable is used in a loop in a read-only
    fashion (i.e., it is referred to by the program or by the
    specification and it is not changed by the loop), it is necessary
    to record the fact that it doesn't change in the loop invariant. */

/* ================================================================= */
/** ** Example: Squaring 

  Here is a program that squares x by repeated addition:

  { x == m }
    y := 0;
    z := 0;
    while y != x {
      z := z + x;
      y := y + 1
    }
  { z == m*m }

/** The first thing to note is that the loop reads x but doesn't
    change its value. As we saw in the previous example, it can be a good idea
    in such cases to add x == m to the invariant.  The other thing
    that we know is often useful in the invariant is the postcondition,
    so let's add that too, leading to the candidate invariant
    [z == m * m && x == m].

    { x == m } ->                                       (a - WRONG)
    { 0 == m*m && x == m }
      y := 0
    { 0 == m*m && x == m };
      z := 0
    { z == m*m && x == m };
      while y != x {
    { z == m*m && x == m && y != x } ->                (c - WRONG)
    { z+x == m*m && x == m }
        z := z + x
    { z == m*m && x = m };
        y := y + 1
    { z == m*m && x == m }
      }
    { z == m*m && x == m && !(y != x) } ->               (b - OK)
    { z == m*m }

    Conditions (a) and (c) fail because of the [z = m*m] part.  While
    [z] starts at [0] and works itself up to [m*m], we can't expect
    [z] to be [m*m] from the start.  If we look at how [z] progresses
    in the loop, after the 1st iteration [z = m], after the 2nd
    iteration [z = 2*m], and at the end [z = m*m].  Since the variable
    [y] tracks how many times we go through the loop, this leads us to
    derive a new invariant candidate: [z == y*m && x == m].

    { x == m } ->                                       (a - OK)
    { 0 == 0*m && x == m }
      y := 0
    { 0 == y*m && x == m };
      z := 0
    { z == y*m && x == m };
      while y != x {
    { z == y*m && x == m && y != x } ->                (c - OK)
    { z+x == (y+1)*m && x == m }
        z := z + x
    { z == (y+1)*m && x = m };
        y := y + 1
    { z == y*m && x == m }
      }
    { z == y*m && x == m && !(y != x) } ->>               (b - OK)
    { z == m*m }

    This new invariant makes the proof go through: all three
    conditions are easy to check.

    It is worth comparing the postcondition [z == m*m] and the [z == y*m] 
    conjunct of the invariant. It is often the case that one has
    to replace parameters with variables -- or with expressions
    involving both variables and parameters, like [m - y] -- when
    going from postconditions to invariants. 
*/

/* ================================================================= */
/** ** Exercise: Factorial 

    Recall that n! denotes the factorial of n (i.e., n! =
    1*2*...*n).  We can easily define it in Dafny as follows:
*/
function fact (n : nat) : nat {
  match n
  case 0 => 1
  case _ => n * (fact(n-1))
}

/* First, write the imperative Dafny program [factorial] that calculates the factorial
   of the number initially stored in the variable x and puts it in
   the variable y.
*/
method factorial(n:nat) returns (x:nat)
  requires true
  ensures (x == fact(n))
{

  var i := n;
  x := 1;

  // x == 1
  // i == n
  // n == n

  // x == fact(n)
  // i == 0
  // n == n 

  // fact(i) * x == fact(n)
  while (i > 0)
    invariant (fact(i) * x == fact(n))
  {
    // { i * (fact(i-1)) * x == fact(n)  && i > 0 }
    // { fact(i-1) * x * i == fact(n)}
    x := x * i;
    i := i - 1;
    
    // { fact(i) * x == fact(n)}
  }
}

/** Using your definition [factorial], write a decorated program that
    implements the factorial function. */

/* ================================================================= */
/** ** Exercise: Minimum 

    { true } ->
    { FILL_IN_HERE }
      x := a
             { FILL_IN_HERE };
      y := b
             { FILL_IN_HERE };
      z := 0
             { FILL_IN_HERE };
      while x != 0 && y != 0 {
             { FILL_IN_HERE } ->
             { FILL_IN_HERE }
        x := x - 1
             { FILL_IN_HERE };
        y := y - 1
             { FILL_IN_HERE };
        z := z + 1
             { FILL_IN_HERE }
      }
    { FILL_IN_HERE } ->
    { z == min a b }
*/

/* ================================================================= */
/** ** Exercise: Two Loops 

    Here is a pretty inefficient way of adding 3 numbers:

     x := 0;
     y := 0;
     z := c;
     while x != a {
       x := x + 1;
       z := z + 1
     };
     while y <> b {
       y := y + 1;
       z := z + 1
     }

    Show that it does what it should by completing the
    following decorated program.

Definition two_loops_dec (a b c : nat) : decorated :=
  <{
    { true } ->>
    { FILL_IN_HERE }
      x := 0
                   { FILL_IN_HERE };
      y := 0
                   { FILL_IN_HERE };
      z := c
                   { FILL_IN_HERE };
      while x != a {
                   { FILL_IN_HERE } ->>
                   { FILL_IN_HERE }
        x := x + 1
                   { FILL_IN_HERE };
        z := z + 1
                   { FILL_IN_HERE }
      end
                   { FILL_IN_HERE } ->>
                   { FILL_IN_HERE };
      while y != b {
                   { FILL_IN_HERE } ->>
                   { FILL_IN_HERE }
        y := y + 1
                   { FILL_IN_HERE };
        z := z + 1
                   { FILL_IN_HERE }
      }
    { FILL_IN_HERE } ->>
    { z == a + b + c }
*/

/* ================================================================= */
/** ** Exercise: Power Series 

    Here is a program that computes the series:
    [1 + 2 + 2^2 + ... + 2^m = 2^(m+1) - 1]

    x := 0;
    y := 1;
    z := 1;
    while x != m {
      z := 2 * z;
      y := y + z;
      x := x + 1;
    }
    end

    Turn this into a decorated program and prove it correct. 
*/

function pow2(n : nat) : nat {
  match n
  case 0 => 1
  case _ => 2 * (pow2 (n-1))
}

/* 
    { true } ->
    { FILL_IN_HERE }
      x := 0
               { FILL_IN_HERE };
      y := 1
               { FILL_IN_HERE };
      z := 1
               { FILL_IN_HERE };
      while x != n {
               { FILL_IN_HERE } ->
               { FILL_IN_HERE }
        z := 2 * z
               { FILL_IN_HERE };
        y := y + z
               { FILL_IN_HERE };
        x := x + 1
               { FILL_IN_HERE }
      }
    { FILL_IN_HERE } ->
    { y == pow2 (n+1) - 1 }
*/