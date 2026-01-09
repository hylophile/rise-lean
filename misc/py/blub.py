import sympy as sp

m_m_5, m_n_4, m_m_26, b_n_0, b_l_0 = sp.symbols(
    "m_m_5 m_n_4 m_m_26 b_n_0 b_l_0", integer=True, positive=True
)
eq0 = sp.Equality(((m_m_5 * (m_n_4**6)) * 2), 128)
eq1 = sp.Equality((m_m_26 * 128), b_n_0)
eq2 = sp.Equality((b_l_0 * m_n_4), (b_l_0 * 2))
res = sp.solvers.solve(
    (
        eq0,
        eq1,
        eq2,
    ),
    (
        m_m_5,
        m_n_4,
        m_m_26,
    ),
    dict=True,
)
if len(res) != 1:
    raise ValueError("did not find unique solution!")
print(res[0])
