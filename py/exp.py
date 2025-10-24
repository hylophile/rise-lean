import sympy as sp

m_n_6, m_n_61, m_n_12, m_n_60, b_w_0, b_h_1 = sp.symbols(
    "m_n_6 m_n_61 m_n_12 m_n_60 b_w_0 b_h_1", integer=True, positive=True
)
m, n = sp.symbols("m n", integer=True, positive=True)
eq0 = sp.Equality((1 + (m_n_6 + ((2 + (2 * (b_w_0 / 2))) - b_w_0))), ((1 + m_n_61) * 2))
eq1 = sp.Equality(
    (1 + (m_n_12 + ((2 + (2 * (b_h_1 / 2))) - b_h_1))), ((1 + m_n_60) * 2)
)
eq2 = sp.Equality(((1 * m_n_61) + 2), ((1 + ((b_w_0 / 2) + 3)) + 0))
eq3 = sp.Equality(((1 * m_n_60) + 2), ((1 + ((b_h_1 / 2) + 3)) + 0))
eq4 = sp.Equality(n, m + 3)
res = sp.solvers.solve((eq0, eq1, eq2, eq3, eq4), (m_n_6, m_n_61, m_n_12, m_n_60, m, n))
print(res)
print(sp.srepr(res))

m_x_55, b_z_23, m, n, b = sp.symbols("m_x_55 b_z_23 m n b", integer=True, positive=True)
# eq0 = sp.Equality((5 + m_x_55), b_z_23)
# eq1 = sp.Equality(2 * (5 + m), n)
eq0 = sp.Equality(m * n, b)
res = sp.solvers.solve((eq0,), (n, m))
print(res)
