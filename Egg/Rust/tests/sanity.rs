use crate::common::*;

#[macro_use]
mod common;

#[test]
fn t_rrr() {
    let r = unify2(
        "(-> (type_mvar a) (type_mvar b))",
        "(-> (type_mvar c) (type_mvar c))",
    )
    .unwrap();
    assert_eq!(
        r,
        map![
            ("(type_mvar b)", "(type_mvar a)"),
            ("(type_mvar c)", "(type_mvar a)")
        ]
    );
}

// #[test]
// fn t_gjewt() {
//     let r = unify2("(array (+ (type_mvar n1) 2) int)", "(array (+ 2 (type_mvar n2)) int)").unwrap();
//     assert_eq!(r, map![]);
// }

// #[test]
// fn t_vhspy() {
//     let r = unify2("(array (+ (type_mvar n1) 2) int)", "(array (+ 3 (type_mvar n2)) int)").unwrap();
//     assert_eq!(r, map![]);
// }

// #[test]
// fn t_c1mju() {
//     let r = unify2("(array (type_mvar n1) int)", "(array (type_mvar n2) int)").unwrap();
//     assert_eq!(r, map![]);
// }

#[test]
fn t_9k0px() {
    let r = unify2("(-> int (type_mvar b))", "(-> f32 (type_mvar c))");
    assert!(r.is_err());
}

#[test]
fn t_lq6oe() {
    let r = unify2("(-> int (type_mvar b))", "(-> bool (type_mvar c))");
    assert!(r.is_err());
}

#[test]
fn t_lr6oe() {
    let r = unify2(
        "(-> (pair (type_mvar a) (type_mvar b)) (type_mvar a))",
        "(-> (type_mvar c) f32)",
    )
    .unwrap();
    assert_eq!(
        r,
        map![
            ("(type_mvar c)", "(pair f32 (type_mvar b))"),
            ("(type_mvar a)", "f32")
        ]
    );
}

#[test]
fn t_ifca8() {
    let r = unify2("(-> int (type_mvar b))", "(-> int (type_mvar c))").unwrap();
    assert_eq!(r, map![("(type_mvar c)", "(type_mvar b)")]);
}

#[test]
fn t_bhru() {
    let r = unify2(
        "(-> (type_mvar a) (type_mvar b))",
        "(-> (type_mvar b) (type_mvar a))",
    )
    .unwrap();
    assert_eq!(r, map![("(type_mvar b)", "(type_mvar a)")]);
}

#[test]
fn t_kxpva() {
    let r = unify2(
        "(-> (pair (type_mvar a) (type_mvar b)) (type_mvar c))",
        "(-> (type_mvar c)                 (type_mvar d))",
    )
    .unwrap();
    assert_eq!(
        r,
        map![
            ("(type_mvar c)", "(pair (type_mvar a) (type_mvar b))"),
            ("(type_mvar d)", "(pair (type_mvar a) (type_mvar b))")
        ]
    );
}

#[test]
fn t_dwz7() {
    let r = unify2("(pair (type_mvar a) (type_mvar b))", "(type_mvar c)").unwrap();
    assert_eq!(
        r,
        map![("(type_mvar c)", "(pair (type_mvar a) (type_mvar b))")]
    );
}

#[test]
fn t_didhl() {
    let r = unify2(
        "(-> (type_mvar a) (-> (type_mvar b) (type_mvar b)))",
        "(-> (type_mvar c) (-> (type_mvar a) (type_mvar a)))",
    )
    .unwrap();
    assert_eq!(
        r,
        map![
            ("(type_mvar b)", "(type_mvar a)"),
            ("(type_mvar c)", "(type_mvar a)")
        ]
    );
}

#[test]
fn t_q05of() {
    let r = unify2(
        "(-> (type_mvar a) (type_mvar b))",
        "(-> (type_mvar a) (type_mvar c))",
    )
    .unwrap();
    assert_eq!(r, map![("(type_mvar c)", "(type_mvar b)")]);
}
#[test]
fn t_qr5of() {
    let r = unify2("(term_mvar a)", "(+ 1 0)").unwrap();
    assert_eq!(r, map![("(term_mvar a)", "1")]);
}
#[test]
fn t_qllof() {
    let r = unify2("(term_mvar a)", "(+ 1 (term_mvar a))");
    assert!(r.is_err());
}
