import sympy as sp

m, n, p, b = sp.symbols("m n p b", integer=True, positive=True)
eq0 = sp.Equality(4 * 128 * 128, m * 4)
eq1 = sp.Equality(n * 4 * 128 * 128, b)
eq2 = sp.Equality(p * 128, m)
res = sp.solvers.solve(
    (eq0, eq1, eq2),
    (m, n, p),
    dict=True,
)
if len(res) != 1:
    raise ValueError("did not find unique solution!")
print(res[0])
