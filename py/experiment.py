from sympy import Eq, Equality, symbols
from sympy.solvers import solve
# from sympy.abc import m, n, b, p, q

a, b, c, m, n, x, y, w, h = symbols(
    "a b c m n x y w h",
    integer=True,
    positive=True,
)

r = solve(Equality(m * m, b), m)
print(r)
r = solve(Equality(m * n, b), m)
print(r)
r = solve(Equality(0, m), m)
print(r)
r = solve(Equality(-4, b), b)
print(r)


eq1 = Eq(x**2 + y**2, 25)
eq2 = Eq(x - y, 1)

solution = solve((eq1, eq2), (x, y))
print(solution)


eqdiv = Equality((2 * n) + 4, ((1 + (w + 3)) + (2 + (2 * ((1 + (w / 2)) - (w / 2))))))
print(solve(eqdiv, n))


eqdiv = Equality(n, 5 / m)
print(
    solve(
        eqdiv,
        n,
        rational=True,
    )
)
