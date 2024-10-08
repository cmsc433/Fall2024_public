# prove bounded integer addition is not associative

from z3 import *
x = BitVec('x', 8)
y = BitVec('y', 8)
z = BitVec('z', 8)
s = Solver()
f  = BV2Int(x+y) + BV2Int(z) == BV2Int(x) + BV2Int(y + z)
s.add(Not(f))
if s.check()== sat:
    print(s.model())
else:
    print("unsat")

