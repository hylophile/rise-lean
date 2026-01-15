import sympy as sp

(
    m_m_1,
    m_m_8,
    m_n_7,
    m_n_0,
    m_n_3,
    m_m_28,
    m_m_30,
    m_n_23,
    m_n_11,
    m_m_12,
    m_n_18,
    m_n_15,
    m_m_26,
    b_n_0,
) = sp.symbols(
    "m_m_1 m_m_8 m_n_7 m_n_0 m_n_3 m_m_28 m_m_30 m_n_23 m_n_11 m_m_12 m_n_18 m_n_15 m_m_26 b_n_0",
    integer=True,
    positive=True,
)
eq0 = sp.Equality(m_m_1, (m_m_8 * m_n_7))
eq1 = sp.Equality(m_n_0, m_n_3)
eq2 = sp.Equality(((4 * 128) * 128), (m_m_28 * 4))
eq3 = sp.Equality(m_n_3, m_m_30)
eq4 = sp.Equality((m_m_30 * ((4 * 128) * 128)), b_n_0)
eq5 = sp.Equality(m_n_7, m_n_23)
eq6 = sp.Equality(m_m_8, (m_n_11 * m_m_12))
eq7 = sp.Equality(m_m_12, m_n_18)
eq8 = sp.Equality(m_n_11, m_n_15)
eq9 = sp.Equality(4, m_n_23)
eq10 = sp.Equality(128, m_n_18)
eq11 = sp.Equality(m_n_15, m_m_26)
eq12 = sp.Equality((m_m_26 * 128), m_m_28)
res = sp.solvers.solve(
    (
        eq0,
        eq1,
        eq2,
        eq3,
        eq4,
        eq5,
        eq6,
        eq7,
        eq8,
        eq9,
        eq10,
        eq11,
        eq12,
    ),
    (
        m_m_1,
        m_m_8,
        m_n_7,
        m_n_0,
        m_n_3,
        m_m_28,
        m_m_30,
        m_n_23,
        m_n_11,
        m_m_12,
        m_n_18,
        m_n_15,
        m_m_26,
    ),
    dict=True,
)
if len(res) != 1:
    raise ValueError("did not find unique solution!")
print(res[0])
