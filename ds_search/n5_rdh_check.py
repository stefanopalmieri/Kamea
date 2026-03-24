"""
Check SAT/UNSAT for a 5x5 Cayley table with:
1. Absorbers (rows 0,1)
2. Exactly 2 absorbers
3. Extensionality (all rows distinct)
4. HasRetractPair
5. HasDichotomy
6. HasICP
"""

from z3 import *

N = 5
CORE = [2, 3, 4]
ABS_SET = [0, 1]

# Cayley table: dot[y][x]
dot = [[Int(f"d_{y}_{x}") for x in range(N)] for y in range(N)]

s = Solver()

# Domain constraints
for y in range(N):
    for x in range(N):
        s.add(dot[y][x] >= 0, dot[y][x] < N)

# 1. Absorbers: row 0 all 0s, row 1 all 1s
for x in range(N):
    s.add(dot[0][x] == 0)
    s.add(dot[1][x] == 1)

# 2. Exactly 2 absorbers: for y in {2,3,4}, NOT(forall x, dot(y,x)=y)
for y in CORE:
    s.add(Not(And([dot[y][x] == y for x in range(N)])))

# 3. Extensionality: all rows pairwise distinct
for y1 in range(N):
    for y2 in range(y1 + 1, N):
        s.add(Or([dot[y1][x] != dot[y2][x] for x in range(N)]))

# 4. HasRetractPair
sec = Int("sec")
ret = Int("ret")
s.add(sec >= 0, sec < N)
s.add(ret >= 0, ret < N)

# Helper: dot_func(a, b) using nested If
def dot_func(a, b):
    """Return a Z3 expression for dot[a][b] where a,b may be Z3 expressions."""
    result = IntVal(0)
    for y in range(N - 1, -1, -1):
        for x in range(N - 1, -1, -1):
            result = If(And(a == y, b == x), dot[y][x], result)
    return result

for x in CORE:
    s.add(dot_func(ret, dot_func(sec, IntVal(x))) == x)
    s.add(dot_func(sec, dot_func(ret, IntVal(x))) == x)
s.add(dot_func(ret, IntVal(0)) == 0)

# 5. HasDichotomy
cls = Int("cls")
s.add(cls >= 2, cls < N)

# cls row maps everything to {0,1}
for x in range(N):
    s.add(Or(dot_func(cls, IntVal(x)) == 0, dot_func(cls, IntVal(x)) == 1))

# Every non-absorber row is either all-core-to-{0,1} or all-core-to-not-{0,1}
for y in CORE:
    all_to_abs = And([Or(dot[y][x] == 0, dot[y][x] == 1) for x in CORE])
    all_to_core = And([And(dot[y][x] != 0, dot[y][x] != 1) for x in CORE])
    s.add(Or(all_to_abs, all_to_core))

# There exists a non-absorber row with a core input mapping outside {0,1}
s.add(Or([And(dot[y][x] != 0, dot[y][x] != 1) for y in CORE for x in CORE]))

# 6. HasICP
a_icp = Int("a_icp")
b_icp = Int("b_icp")
c_icp = Int("c_icp")
s.add(a_icp >= 2, a_icp < N)
s.add(b_icp >= 2, b_icp < N)
s.add(c_icp >= 2, c_icp < N)
# Pairwise distinct
s.add(a_icp != b_icp, a_icp != c_icp, b_icp != c_icp)

# b preserves core
for x in CORE:
    s.add(And(dot_func(b_icp, IntVal(x)) != 0, dot_func(b_icp, IntVal(x)) != 1))

# Factorization: a(x) = c(b(x)) for core x
for x in CORE:
    s.add(dot_func(a_icp, IntVal(x)) == dot_func(c_icp, dot_func(b_icp, IntVal(x))))

# Non-triviality: exists x,y in core with a(x) != a(y)
s.add(Or([dot_func(a_icp, IntVal(x)) != dot_func(a_icp, IntVal(y))
          for x in CORE for y in CORE if x < y]))

print("Checking SAT...")
result = s.check()
print(f"Result: {result}")

if result == sat:
    m = s.model()
    print("\nCayley table (dot[y][x]):")
    print("    x=", list(range(N)))
    for y in range(N):
        row = [m.evaluate(dot[y][x]).as_long() for x in range(N)]
        print(f"y={y}: {row}")
    print(f"\nsec={m.evaluate(sec)}, ret={m.evaluate(ret)}")
    print(f"cls={m.evaluate(cls)}")
    print(f"a_icp={m.evaluate(a_icp)}, b_icp={m.evaluate(b_icp)}, c_icp={m.evaluate(c_icp)}")
else:
    print("UNSAT confirmed.")
