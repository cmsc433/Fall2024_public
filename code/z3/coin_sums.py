# Solving Problem Euler 31: “Coin sums”

# In the United Kingdom the currency is made up of pound (£) and pence (p). 
# There are eight coins in general circulation:
# 1p, 2p, 5p, 10p, 20p, 50p, £1 (100p), and £2 (200p).
# It is possible to make £2 in the following way:
# 1×£1 + 1×50p + 2×20p + 1×5p + 1×2p + 3×1p
# How many different ways can £2 be made using any number of coins?

#!/usr/bin/python3
from z3 import *
a,b,c,d,e,f,g,h = Ints('a b c d e f g h')
s = Solver()
s.add(1*a + 2*b + 5*c + 10*d + 20*e + 50*f + 100*g + 200*h == 200,a>=0, b>=0, c>=0, d>=0, e>=0, f>=0, g>=0, h>=0) 
result =[]
while True:
    if s.check() == sat:
        m = s.model()
        print (m)
        result.append(m)
        # Create a new constraint the blocks the current model 
        block = []
        for d in m:
            # create a constant from declaration
            c=d()
            block.append(c != m[d]) 
        s.add(Or (block))
    else:
        print (len(result))
        break
