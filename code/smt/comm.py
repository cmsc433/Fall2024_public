from z3 import *
x = BitVec('x', 8)
y = BitVec('y', 8)
s = Solver()
f  = BV2Int(x) + BV2Int(y) == BV2Int(y) + BV2Int(x)
s.add(Not(f))
if s.check()== sat:
    print(s.model())
else:
    print("unsat")

#solve(BV2Int(x)+1 != BV2Int(x+1))