#### Rabbits and Chickens

# Uncle Henry has 48 rabbits and chickens. He knows his rabbits 
# and chickens have 108 legs, but does not know the exact number 
# of rabbits and chickens. Can you help him? How many rabbits and 
# chickens does Uncle Henry have?

from z3 import *

rabbit, chicken = Ints('rabbit chicken')
s = Solver()
s.add(rabbit + chicken == 48) # 48 animals
s.add(4 * rabbit + 2 * chicken == 108) # 108 legs

 # solve the constraints
if s.check() == unsat: 
    print('No solution!')
    sys.exit(1)
print(s.model()) # get the solution