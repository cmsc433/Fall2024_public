#  circle + circle = 10
#  circle * square + sqaure = 12
# circle * square - triangle * circle = circle
# What is th evalue of the triangle?


#!/ usr/bin/ python
from z3 import *
circle , square , triangle = Ints('circle square triangle')
s = Solver()
s.add( circle + circle ==10)
s.add( circle * square + square ==12)
s.add( circle *square - triangle * circle == circle )
if s.check() == unsat:
    print("UNSAT")
else:
    print (s.model())