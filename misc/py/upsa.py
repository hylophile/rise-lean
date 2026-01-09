import sympy as sp

(
    m_m_66,
    m_n_65,
    m_m_7,
    m_n_27,
    m_m_28,
    m_n_1,
    m_n_10,
    m_m_13,
    m_n_16,
    m_m_17,
    m_n_24,
    m_n_20,
    m_n_43,
    m_m_31,
    m_n_41,
    m_n_37,
    m_n_30,
    m_n_34,
    m_n_52,
    m_n_49,
    m_m_61,
    m_n_60,
    m_n_48,
    m_n_5,
    b_w_0,
    b_h_1,
) = sp.symbols(
    "m_m_66 m_n_65 m_m_7 m_n_27 m_m_28 m_n_1 m_n_10 m_m_13 m_n_16 m_m_17 m_n_24 m_n_20 m_n_43 m_m_31 m_n_41 m_n_37 m_n_30 m_n_34 m_n_52 m_n_49 m_m_61 m_n_60 m_n_48 m_n_5 b_w_0 b_h_1",
    integer=True,
    positive=True,
)
eq0 = sp.Equality(((b_w_0 / 2) + 3), m_m_66)
eq1 = sp.Equality(((b_h_1 / 2) + 3), m_n_65)
eq2 = sp.Equality((1 + m_m_7), (m_n_27 * m_m_28))
eq3 = sp.Equality(m_n_1, m_n_10)
eq4 = sp.Equality((m_n_10 + ((2 + (2 * (b_h_1 / 2))) - b_h_1)), m_m_13)
eq5 = sp.Equality((1 + m_m_13), (m_n_16 * m_m_17))
eq6 = sp.Equality(m_m_17, m_n_24)
eq7 = sp.Equality(m_n_16, m_n_20)
eq8 = sp.Equality(m_m_28, m_n_43)
eq9 = sp.Equality(m_m_31, m_n_41)
eq10 = sp.Equality(m_n_37, m_n_30)
eq11 = sp.Equality(m_n_20, m_n_34)
eq12 = sp.Equality(2, m_n_52)
eq13 = sp.Equality(2, m_n_49)
eq14 = sp.Equality((((m_m_61 + 1) - 2) / 1), m_n_37)
eq15 = sp.Equality(m_n_34, (((m_n_60 + 1) - 2) / 1))
eq16 = sp.Equality(m_m_61, ((1 + m_m_66) + 0))
eq17 = sp.Equality(m_n_60, ((1 + m_n_65) + 0))
eq18 = sp.Equality(m_n_41, 2)
eq19 = sp.Equality(m_n_43, 2)
eq20 = sp.Equality(m_n_48, 2)
eq21 = sp.Equality(2, 2)
eq22 = sp.Equality(2, 2)
eq23 = sp.Equality(m_n_52, 2)
eq24 = sp.Equality(2, 2)
eq25 = sp.Equality(2, 2)
eq26 = sp.Equality(m_n_48, m_n_49)
eq27 = sp.Equality(m_n_30, m_n_27)
eq28 = sp.Equality(m_n_24, m_m_31)
eq29 = sp.Equality((m_n_5 + ((2 + (2 * (b_w_0 / 2))) - b_w_0)), m_m_7)
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
        eq13,
        eq14,
        eq15,
        eq16,
        eq17,
        eq18,
        eq19,
        eq20,
        eq21,
        eq22,
        eq23,
        eq24,
        eq25,
        eq26,
        eq27,
        eq28,
        eq29,
    ),
    (
        m_m_66,
        m_n_65,
        m_m_7,
        m_n_27,
        m_m_28,
        m_n_1,
        m_n_10,
        m_m_13,
        m_n_16,
        m_m_17,
        m_n_24,
        m_n_20,
        m_n_43,
        m_m_31,
        m_n_41,
        m_n_37,
        m_n_30,
        m_n_34,
        m_n_52,
        m_n_49,
        m_m_61,
        m_n_60,
        m_n_48,
        m_n_5,
    ),
    dict=True,
)
if len(res) != 1:
    raise ValueError("did not find unique solution!")
print(res[0])
