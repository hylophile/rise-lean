import sympy as sp
from sympy.solvers import solve

m_n_6, m_n_61, m_n_12, m_n_60, b_w_0, b_h_1 = sp.symbols(
    "m_n_6 m_n_61 m_n_12 m_n_60 b_w_0 b_h_1", integer=True, positive=True
)
eq0 = sp.Equality((1 + (m_n_6 + ((2 + (2 * (b_w_0 / 2))) - b_w_0))), ((1 + m_n_61) * 2))
eq1 = sp.Equality((1 + (m_n_12 + ((2 + (2 * (b_h_1 / 2))) - b_h_1))), ((1 + m_n_60) * 2))
eq2 = sp.Equality(((1 * m_n_61) + 2), ((1 + ((b_w_0 / 2) + 3)) + 0))
eq3 = sp.Equality(((1 * m_n_60) + 2), ((1 + ((b_h_1 / 2) + 3)) + 0))
res = solve((eq0, eq1, eq2, eq3), (m_n_6, m_n_61, m_n_12, m_n_60))
print(sp.srepr(res))
