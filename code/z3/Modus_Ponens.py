from z3 import *

set_param(proof=True)
s = Solver()
p,q = Bools("p q")
s.add(q)
s.add(Not(p))
s.add(Implies(p,q))
if s.check() == sat:
    print (s.model())