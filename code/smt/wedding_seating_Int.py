
# Encode the placement of wedding guests in Z3
# Model assignment via nine boolean variables 
# Alice does not sit next to Charlie
# Alice does not sit on the leftmost chair
# Bob does not sit to the right of Charlie
# Each person gets a chair
# Every person gets at most one chair § Every chair gets at most one person


from z3 import *

def print_result(m):
    for i in ['a','b','c']:
        for j in ['l','m','r']:
            if(m.evaluate(vars[f'x{i}{j}']) == 1):
               print(f'x{i}{j}')

# create the variables
vars = {}
for i in ['a','b','c']:
    for j in ['l','m','r']:
        v = f'x{i}{j}'
        vars[v] = Int(v)

# xam == 1 if alice takes the left seat
# variables can have the value 0 or 1
t = []
for i in ['a','b','c']:
    for j in ['l','m','r']:
        v = f'x{i}{j}'
        t.append(Or(vars[v] == 0,  vars[v] == 1))


s = Solver()
s.add(And(t))
# Alice does not sit next to Charlie
s.add(And(Implies(Or(vars['xal']==1, vars['xar']==1), (vars['xcm'] != 1) ), 
          Implies(vars['xam']==1, And(vars['xcl']!=1, vars['xcr']!=1))))

# Alice does not sit on the leftmost chair
s.add(vars['xal'] != 1)


# Bob does not sit to the right of Charlie
#s.add(And(Implies(vars['xcl']==1, vars['xbm']!=1), Implies(vars['xcm']==1, vars['xbr'] != 1)))

#Each person gets a chair
for i in ['a','b','c']:
    t=0
    for j in ['l','m','r']:
        t = t + vars[f'x{i}{j}']
    s.add(t == 1)
   


# Every chair gets at most one person
for i in ['l','m','r']:
    t=0
    for j in ['a','b','c']:
        t = t + vars[f'x{j}{i}']
    s.add(t == 1)

if s.check() == sat:
    m = s.model()
    print_result(m)
else:
    print("UNSAT")