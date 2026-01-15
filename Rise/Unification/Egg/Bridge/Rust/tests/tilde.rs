//
use crate::common::*;
use egg_unify::lang::*;

#[macro_use]
mod common;

#[test]
fn ut1() {
    // eq2 = sp.Equality((1+m_m_7), (m_n_27*m_m_28))
    // let r = unifyt("(~ (+ 1 (nat_mvar m_7)) (* (nat_mvar m_27) (nat_mvar m_28)))").unwrap();
    // let r = unify("(~ (+ 1 (nat_mvar m_7)) (* (nat_bvar m_27) (nat_bvar m_28)))").unwrap();
    let r = unify("5=(+ (nat_mvar m_7) 1)").unwrap();
    // let r = unifyt("(~ (+ 1 (nat_mvar m_7)) 5)").unwrap();
    assert_eq!(
        r,
        map![
            ("(data_mvar b)", "(data_mvar a)"),
            ("(data_mvar c)", "(data_mvar a)")
        ]
    );
}
// #[test]
// fn u2() {
//     // eq2 = sp.Equality((1+m_m_7), (m_n_27*m_m_28))
//     // let r = unifyt("(~ (+ 1 (nat_mvar m_7)) (* (nat_mvar m_27) (nat_mvar m_28)))").unwrap();
//     // let r = unify("(~ (+ 1 (nat_mvar m_7)) (* (nat_bvar m_27) (nat_bvar m_28)))").unwrap();
//     // let r = unifyt("(~ 5 (+ 1 (nat_mvar m_7)))").unwrap();
//     let r = unifyt("(~ (nat_mvar m_7) 5)").unwrap();
//     assert_eq!(
//         r,
//         map![
//             ("(data_mvar b)", "(data_mvar a)"),
//             ("(data_mvar c)", "(data_mvar a)")
//         ]
//     );
// }
