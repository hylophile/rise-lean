import sympy as sp

m_m_1, m_m_5, m_n_0, m_m_3, b_a_2, b_b_1, b_m_0 = sp.symbols(
    "m_m_1 m_m_5 m_n_0 m_m_3 b_a_2 b_b_1 b_m_0", integer=True, positive=True
)
eq0 = sp.Equality((b_a_2 - b_b_1), (b_a_2 + b_b_1))
eq1 = sp.Equality(m_m_1, m_m_5)
eq2 = sp.Equality((m_m_5 * (b_a_2 - b_b_1)), b_m_0)
eq3 = sp.Equality(m_n_0, m_m_3)
eq4 = sp.Equality((m_m_3 * (b_a_2 + b_b_1)), b_m_0)
res = sp.solvers.solve(
    (
        eq0,
        eq1,
        eq2,
        eq3,
        eq4,
    ),
    (
        m_m_1,
        m_m_5,
        m_n_0,
        m_m_3,
    ),
    dict=True,
)
if len(res) != 1:
    raise ValueError("did not find unique solution!")
print(res[0])
