# Calculate two integers a and b, where a * b == 1000, 
# and a+b is the minimum among all the solutions.

from z3 import *
s = Optimize()
a = Int('a')
b = Int('b')

s.add(a * b == 1000)
s.add(And(a > 0, b > 0))
s.minimize(a + b)
if s.check() == sat:
    print(s.model())
else: 
    print("UNSAT")
# [b = 40, a = 25]