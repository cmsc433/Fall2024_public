# Solving the Eight queens puzzle
# https://en.wikipedia.org/wiki/Eight_queens_puzzle


from z3 import *
N = 8

def var(row, col):
    return Int(f'cell_{row}_{col}')


vs = [ [ var(row, col) for col in range(N) ] for row in range(N) ]
cells_defined = [
      And(0 <= vs[i][j], vs[i][j] <= 1)
      for i in range(N) for j in range(N)
    ]
s = Solver()
s.add(cells_defined)
rows_ok = [Sum(vs[i]) == 1 for i in range(N)]

# all entries within a column must be distinct
cols_ok = [Sum([vs[i][j] for i in range(N)]) == 1 for j in range(N) ]

diagonals_ok = [Implies( And(vs[i][j] == 1, vs[k][h] == 1, i != k, j != h), abs(k - i) != abs(j - h))
    for i in range(N) for j in range(N) 
    for k in range(N) for h in range(N)]

s.add(rows_ok)
s.add(cols_ok)
s.add(diagonals_ok)
if s.check() == sat:
    m = s.model()
    for i in range(N):
        for j in range(N):
            if m[var(i,j)] == 1:
                print(m[var(i,j)],end ="|")
            else:
                print(" ",end ="|")
        print("\n---------------")
else:
    print("unsat")