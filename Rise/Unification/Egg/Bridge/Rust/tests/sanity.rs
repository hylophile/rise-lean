use crate::common::*;

#[macro_use]
mod common;

#[test]
fn t_rrr() {
    let r = unify2(
        "(-> (data_mvar a) (data_mvar b))",
        "(-> (data_mvar c) (data_mvar c))",
    )
    .unwrap();
    assert_eq!(
        r,
        map![
            ("(data_mvar b)", "(data_mvar a)"),
            ("(data_mvar c)", "(data_mvar a)")
        ]
    );
}

// #[test]
// fn t_gjewt() {
//     let r = unify2("(array (+ (data_mvar n1) 2) int)", "(array (+ 2 (data_mvar n2)) int)").unwrap();
//     assert_eq!(r, map![]);
// }

// #[test]
// fn t_vhspy() {
//     let r = unify2("(array (+ (data_mvar n1) 2) int)", "(array (+ 3 (data_mvar n2)) int)").unwrap();
//     assert_eq!(r, map![]);
// }

// #[test]
// fn t_c1mju() {
//     let r = unify2("(array (data_mvar n1) int)", "(array (data_mvar n2) int)").unwrap();
//     assert_eq!(r, map![]);
// }

#[test]
fn t_9k0px() {
    let r = unify2("(-> int (data_mvar b))", "(-> f32 (data_mvar c))");
    assert!(r.is_err());
}

#[test]
fn t_lq6oe() {
    let r = unify2("(-> int (data_mvar b))", "(-> bool (data_mvar c))");
    assert!(r.is_err());
}

#[test]
fn t_lr6oe() {
    let r = unify2(
        "(-> (pair (data_mvar a) (data_mvar b)) (data_mvar a))",
        "(-> (data_mvar c) f32)",
    )
    .unwrap();
    assert_eq!(
        r,
        map![
            ("(data_mvar c)", "(pair f32 (data_mvar b))"),
            ("(data_mvar a)", "f32")
        ]
    );
}

#[test]
fn t_ifca8() {
    let r = unify2("(-> int (data_mvar b))", "(-> int (data_mvar c))").unwrap();
    assert_eq!(r, map![("(data_mvar c)", "(data_mvar b)")]);
}

#[test]
fn t_bhru() {
    let r = unify2(
        "(-> (data_mvar a) (data_mvar b))",
        "(-> (data_mvar b) (data_mvar a))",
    )
    .unwrap();
    assert_eq!(r, map![("(data_mvar b)", "(data_mvar a)")]);
}

#[test]
fn t_kxpva() {
    let r = unify2(
        "(-> (pair (data_mvar a) (data_mvar b)) (data_mvar c))",
        "(-> (data_mvar c)                 (data_mvar d))",
    )
    .unwrap();
    assert_eq!(
        r,
        map![
            ("(data_mvar c)", "(pair (data_mvar a) (data_mvar b))"),
            ("(data_mvar d)", "(pair (data_mvar a) (data_mvar b))")
        ]
    );
}

#[test]
fn t_dwz7() {
    let r = unify2("(pair (data_mvar a) (data_mvar b))", "(data_mvar c)").unwrap();
    assert_eq!(
        r,
        map![("(data_mvar c)", "(pair (data_mvar a) (data_mvar b))")]
    );
}

#[test]
fn t_didhl() {
    let r = unify2(
        "(-> (data_mvar a) (-> (data_mvar b) (data_mvar b)))",
        "(-> (data_mvar c) (-> (data_mvar a) (data_mvar a)))",
    )
    .unwrap();
    assert_eq!(
        r,
        map![
            ("(data_mvar b)", "(data_mvar a)"),
            ("(data_mvar c)", "(data_mvar a)")
        ]
    );
}

#[test]
fn t_q05of() {
    let r = unify2(
        "(-> (data_mvar a) (data_mvar b))",
        "(-> (data_mvar a) (data_mvar c))",
    )
    .unwrap();
    assert_eq!(r, map![("(data_mvar c)", "(data_mvar b)")]);
}
#[test]
fn t_qr5of() {
    let r = unify2("(nat_mvar a)", "(+ 1 0)").unwrap();
    assert_eq!(r, map![("(nat_mvar a)", "1")]);
}
// #[test]
// fn t_qllof() {
//     let r = unify2("(nat_mvar a)", "(+ 1 (nat_mvar a))");
//     assert!(r.is_err());
// }
