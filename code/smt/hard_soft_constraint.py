# We can add soft constraints. These are assertions, optionally annotated with weights. 
# The objective is to satisfy as many soft constraints as possible in a solution. 
# When weights are used, the objective is to find a solution with the least penalty,
#  given by the sum of weights, for unsatisfied constraints. 

from z3 import *

x = Bool('x')
y = Bool('y')
z = Bool('z')

s = Optimize()
s.add(And(x,Or(y,z)))
s.add_soft(Not(y), weight=15)
s.add_soft(Not(z), weight=10)

print(s.check())
print(s.model())

# [y = False, z1 = True, x = True]
# y has a bigger penalty than z. It found a solution with least penalty. 
