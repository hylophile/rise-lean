use egg_unify::lang::unify;

use crate::common::*;

#[macro_use]
mod common;

#[test]
fn t_blub() {
    let r = unify2(
        "(array (term_mvar n_1) (array (+ 1 (+ (term_mvar n_5) (- (+ 2 (* 2 (/ (term_bvar w_0) 2))) (term_bvar w_0)))) (type_mvar t_8)))",
        "(array (term_mvar n_10) (array (* (+ 1 (/ (- (+ (+ 1 (term_mvar m_66)) 0) 2) 1)) 2) f32))")
    .unwrap();

    assert_eq!(r, map![("(term_mvar a)", "1")]);
    // !(term_mvar n_10)=(term_mvar n_1);(type_mvar t_8)=f32
}

#[test]
fn t_lapl_upsamp() {
    let goals="(type_mvar anonymous_0)=(array (+ (/ (term_bvar h_1) 2) 3) (array (+ (/ (term_bvar w_0) 2) 3) f32));(array (term_mvar n_1) (type_mvar s_2))=(array (term_mvar n_10) (type_mvar d_11));(type_mvar anonymous_9)=(type_mvar anonymous_0);(array (+ (term_mvar n_10) (- (+ 2 (* 2 (/ (term_bvar h_1) 2))) (term_bvar h_1))) (type_mvar d_11))=(array (term_mvar m_13) (type_mvar t_14));(type_mvar anonymous_12)=(type_mvar anonymous_9);(array (+ 1 (term_mvar m_13)) (type_mvar t_14))=(array (* (term_mvar n_16) (term_mvar m_17)) (type_mvar t_18));(type_mvar anonymous_15)=(type_mvar anonymous_12);(array (term_mvar n_16) (array (term_mvar m_17) (type_mvar t_18)))=(array (term_mvar n_20) (type_mvar t_22));(type_mvar anonymous_19)=(type_mvar anonymous_15);(array (term_mvar n_20) (type_mvar s_21))=(array (term_mvar n_34) (type_mvar t_36));(type_mvar anonymous_33)=(type_mvar anonymous_19);(array (term_mvar n_34) (type_mvar s_35))=(array (+ 1 (/ (- (term_mvar n_60) 2) 1)) (array (+ 1 (/ (- (term_mvar m_61) 2) 1)) (array 2 (array 2 (type_mvar d_62)))));(type_mvar anonymous_57)=(type_mvar anonymous_33);(array (term_mvar n_60) (array (term_mvar m_61) (type_mvar d_62)))=(array (+ (+ 1 (term_mvar n_65)) 0) (array (+ (+ 1 (term_mvar m_66)) 0) (type_mvar d_67)));(array (term_mvar n_65) (array (term_mvar m_66) (type_mvar d_67)))=(type_mvar anonymous_57);(-> (type_mvar s_35) (type_mvar t_36))=(-> (array (term_mvar n_37) (type_mvar s_38)) (array (term_mvar n_37) (type_mvar t_39)));(-> (type_mvar s_38) (type_mvar t_39))=(-> (type_mvar anonymous_40) (array (term_mvar n_41) (type_mvar t_42)));(-> (index (term_mvar n_41)) (type_mvar t_42))=(-> (index 2) (array (term_mvar n_43) (type_mvar t_44)));(-> (index (term_mvar n_43)) (type_mvar t_44))=(-> (index 2) f32);(type_mvar anonymous_45)=(type_mvar t_55);(type_mvar t_55)=(array 2 f32);(type_mvar t_55)=(array 2 f32);bool=bool;(type_mvar t_56)=(index 2);(type_mvar t_56)=(index 2);(type_mvar anonymous_46)=(type_mvar t_53);(type_mvar t_53)=(array 2 f32);(type_mvar t_53)=(array 2 f32);bool=bool;(type_mvar t_54)=(index 2);(type_mvar t_54)=(index 2);(type_mvar anonymous_47)=(type_mvar anonymous_40);(array (term_mvar n_48) f32)=(array (term_mvar n_49) (type_mvar t_51));(array (term_mvar n_49) (type_mvar s_50))=(type_mvar anonymous_47);(-> (type_mvar s_50) (type_mvar t_51))=(-> (array (term_mvar n_52) f32) f32);(array (term_mvar n_52) f32)=(type_mvar anonymous_46);(array (term_mvar n_48) f32)=(type_mvar anonymous_45);(-> (type_mvar s_21) (type_mvar t_22))=(-> (type_mvar anonymous_23) (array (term_mvar n_24) (type_mvar t_26)));(array (term_mvar n_24) (type_mvar s_25))=(array (term_mvar m_31) (array (term_mvar n_30) (type_mvar t_32)));(array (term_mvar n_30) (array (term_mvar m_31) (type_mvar t_32)))=(type_mvar anonymous_23);(-> (type_mvar s_25) (type_mvar t_26))=(-> (array (term_mvar n_27) (array (term_mvar m_28) (type_mvar t_29))) (array (* (term_mvar n_27) (term_mvar m_28)) (type_mvar t_29)));(-> (type_mvar s_2) (type_mvar t_3))=(-> (type_mvar anonymous_4) (array (term_mvar n_5) (type_mvar d_6)));(array (+ (term_mvar n_5) (- (+ 2 (* 2 (/ (term_bvar w_0) 2))) (term_bvar w_0))) (type_mvar d_6))=(array (term_mvar m_7) (type_mvar t_8));(array (+ 1 (term_mvar m_7)) (type_mvar t_8))=(type_mvar anonymous_4)";
    let r = unify(goals).unwrap();
    assert_eq!(r, map![]);
}

#[test]
fn t_downsample() {
    let _goals="(array (term_mvar n_31) (array (term_mvar m_32) f32))=(array (+ (term_bvar h_1) 3) (array (+ (term_bvar w_0) 3) f32));(array (term_mvar n_1) (array (term_mvar n_4) (array 4 (array 4 f32))))=(array (+ 1 (term_mvar n_21)) (array (+ 1 (term_mvar n_27)) (array 4 (array 4 (type_mvar d_33)))));(array (term_mvar n_31) (array (term_mvar m_32) (type_mvar d_33)))=(type_mvar anonymous_0);(array (term_mvar n_14) (array (term_mvar n_17) (array (term_mvar m_18) (type_mvar t_19))))=(array (+ 1 (term_mvar n_21)) (array 4 (array (+ 1 (term_mvar n_27)) (array 4 (type_mvar d_33)))));(array (term_mvar n_31) (array (term_mvar m_32) (type_mvar d_33)))=(type_mvar anonymous_13);(array (+ (* 2 (term_mvar n_21)) 4) (type_mvar t_22))=(array (+ (+ 1 (term_mvar n_31)) (+ 2 (* 2 (- (+ 1 (/ (term_bvar h_1) 2)) (/ (term_bvar h_1) 2))))) (array (+ 1 (term_mvar n_27)) (array 4 (type_mvar d_33))));(array (term_mvar n_31) (array (term_mvar m_32) (type_mvar d_33)))=(type_mvar anonymous_20);(array (term_mvar n_24) (array (+ (* 2 (term_mvar n_27)) 4) (type_mvar t_28)))=(array (+ (+ 1 (term_mvar n_31)) (+ 2 (* 2 (- (+ 1 (/ (term_bvar h_1) 2)) (/ (term_bvar h_1) 2))))) (array (+ (+ 1 (term_mvar m_32)) (+ 2 (* 2 (- (+ 1 (/ (term_bvar w_0) 2)) (/ (term_bvar w_0) 2))))) (type_mvar d_33)));(array (term_mvar n_31) (array (term_mvar m_32) (type_mvar d_33)))=(type_mvar anonymous_23);(-> (type_mvar s_25) (type_mvar t_26))=(-> (array (+ (* 2 (term_mvar n_27)) 4) (type_mvar t_28)) (array (+ 1 (term_mvar n_27)) (array 4 (type_mvar t_28))));(-> (type_mvar s_15) (type_mvar t_16))=(-> (array (term_mvar n_17) (array (term_mvar m_18) (type_mvar t_19))) (array (term_mvar m_18) (array (term_mvar n_17) (type_mvar t_19))));(-> (type_mvar s_2) (type_mvar t_3))=(-> (array (term_mvar n_4) (array 4 (array 4 f32))) (array (term_mvar n_4) f32));(-> (type_mvar s_5) (type_mvar t_6))=(-> (array 4 (array 4 f32)) f32);(array 4 f32)=(array (term_mvar n_9) f32);(array (term_mvar n_9) (array 4 f32))=(type_mvar anonymous_7);(-> (type_mvar s_10) (type_mvar t_11))=(-> (array 4 f32) f32);(array (term_mvar n_12) f32)=(array 4 f32);(array (term_mvar n_8) f32)=(array 4 f32)";
    let goals="(array (term_mvar n_31) (array (term_mvar m_32) f32))=(array (+ (term_bvar h_1) 3) (array (+ (term_bvar w_0) 3) f32));(array (term_mvar n_24) (array (+ (* 2 (term_mvar n_27)) 4) (type_mvar t_28)))=(array (+ (+ 1 (term_mvar n_31)) (+ 2 (* 2 (- (+ 1 (/ (term_bvar h_1) 2)) (/ (term_bvar h_1) 2))))) (array (+ (+ 1 (term_mvar m_32)) (+ 2 (* 2 (- (+ 1 (/ (term_bvar w_0) 2)) (/ (term_bvar w_0) 2))))) (type_mvar d_33)))";
    let r = unify(goals).unwrap();
    pp(&r);
    assert_eq!(r, map![]);
}

#[test]
fn t_droplast() {
    let goals ="(array (+ (term_bvar n_1) (term_mvar m_0)) (type_mvar t_1))=(array (+ (term_bvar n_1) (term_bvar m_2)) (type_bvar d_0))";
    let r = unify(goals).unwrap();
    assert_eq!(r, map![]);
}

#[test]
fn t_scalintel() {
    let goals = "(array (term_mvar n_0) (array (term_mvar m_1) (type_mvar t_2)))=(array (term_mvar n_3) (type_mvar t_5));(array (term_mvar n_3) (type_mvar s_4))=(array (term_mvar m_30) (array (* (* 4 128) 128) (type_mvar t_31)));(array (* (term_mvar m_30) (* (* 4 128) 128)) (type_mvar t_31))=(array (term_bvar n_0) f32);(-> (type_mvar s_4) (type_mvar t_5))=(-> (type_mvar anonymous_6) (array (* (term_mvar m_8) (term_mvar n_7)) (type_mvar t_9)));(array (term_mvar m_8) (vector (term_mvar n_7) (type_mvar t_9)))=(array (* (term_mvar n_11) (term_mvar m_12)) (type_mvar t_13));(type_mvar anonymous_10)=(type_mvar anonymous_6);(array (term_mvar n_11) (array (term_mvar m_12) (type_mvar t_13)))=(array (term_mvar n_15) (type_mvar t_17));(type_mvar anonymous_14)=(type_mvar anonymous_10);(array (term_mvar n_15) (type_mvar s_16))=(array (term_mvar m_26) (array 128 (type_mvar t_27)));(type_mvar anonymous_25)=(type_mvar anonymous_14);(array (* (term_mvar m_26) 128) (type_mvar t_27))=(array (term_mvar m_28) (vector 4 (type_mvar t_29)));(array (* (term_mvar m_28) 4) (type_mvar t_29))=(type_mvar anonymous_25);(-> (type_mvar s_16) (type_mvar t_17))=(-> (array (term_mvar n_18) (type_mvar s_19)) (array (term_mvar n_18) (type_mvar t_20)));(-> (type_mvar s_19) (type_mvar t_20))=(-> (type_mvar anonymous_21) (type_mvar t_22));(type_mvar t_22)=(vector (term_mvar n_23) (type_mvar t_24));(type_mvar t_24)=f32;(type_mvar t_22)=(type_mvar anonymous_21)";
    let r = unify(goals).unwrap();
    assert_eq!(r, map![]);
}
#[test]
fn t_padclamp2d() {
    let goals="(type_mvar anonymous_0)=(array (term_bvar n_2) (array (term_bvar m_1) (type_bvar d_0)));(array (term_mvar n_1) (type_mvar t_2))=(array (term_mvar n_3) (type_mvar t_5));(array (term_mvar n_3) (type_mvar s_4))=(type_mvar anonymous_0);(-> (type_mvar s_4) (type_mvar t_5))=(-> (array (term_mvar n_6) (type_mvar t_7)) (array (+ (+ (term_bvar lInner_4) (term_mvar n_6)) (term_bvar rInner_3)) (type_mvar t_7)))";
    let r = unify(goals).unwrap();
    assert_eq!(r, map![]);
}

#[test]
fn t_simpslide2d4() {
    let goals="(type_mvar anonymous_0)=(array (term_bvar n_2) (array (term_bvar m_1) (type_bvar d_0)));(array (term_mvar n_1) (type_mvar s_2))=(array (+ 1 (term_mvar n_8)) (array (term_bvar szOuter_6) (type_mvar t_9)));(type_mvar anonymous_7)=(type_mvar anonymous_0);(array (+ (* (term_bvar stOuter_5) (term_mvar n_8)) (term_bvar szOuter_6)) (type_mvar t_9))=(array (term_mvar n_10) (type_mvar t_12));(array (term_mvar n_10) (type_mvar s_11))=(type_mvar anonymous_7)";
    let r = unify(goals).unwrap();
    assert_eq!(r, map![]);
}
#[test]
fn t_slide2d4() {
    let goals="(type_mvar anonymous_0)=(array (term_bvar n_2) (array (term_bvar m_1) (type_bvar d_0)));(array (term_mvar n_1) (type_mvar s_2))=(array (+ 1 (term_mvar n_8)) (array (term_bvar szOuter_6) (type_mvar t_9)));(type_mvar anonymous_7)=(type_mvar anonymous_0);(array (+ (* (term_bvar stOuter_5) (term_mvar n_8)) (term_bvar szOuter_6)) (type_mvar t_9))=(array (term_mvar n_10) (type_mvar t_12));(array (term_mvar n_10) (type_mvar s_11))=(type_mvar anonymous_7);(-> (type_mvar s_11) (type_mvar t_12))=(-> (array (+ (* (term_bvar stInner_3) (term_mvar n_13)) (term_bvar szInner_4)) (type_mvar t_14)) (array (+ 1 (term_mvar n_13)) (array (term_bvar szInner_4) (type_mvar t_14))));(-> (type_mvar s_2) (type_mvar t_3))=(-> (array (term_mvar n_4) (array (term_mvar m_5) (type_mvar t_6))) (array (term_mvar m_5) (array (term_mvar n_4) (type_mvar t_6))))";
    let r = unify(goals).unwrap();
    assert_eq!(r, map![]);
}

#[test]
fn t_scalt() {
    //     let goals="(array (term_mvar n_0) (array (term_mvar m_1) (type_mvar t_2)))=(array (term_mvar m_3) (array (* (* 4 128) 128) (type_mvar t_4)));(array (* (term_mvar m_3) (* (* 4 128) 128)) (type_mvar t_4))=(array (term_bvar n_0) f32)
    // ";
    let goals ="(array (term_mvar n_0) (array (term_mvar m_1) (type_mvar t_2)))=(array (term_mvar m_3) (array 2 (type_mvar t_4)));(array (* (term_mvar m_3) 2) (type_mvar t_4))=(array (term_mvar m_5) (array (* (* 4 128) 128) (type_mvar t_6)));(array (* (term_mvar m_5) (* (* 4 128) 128)) (type_mvar t_6))=(array (term_bvar n_0) f32)";

    let r = unify(goals).unwrap();
    pp(&r);
    assert_eq!(r, map![]);
}

#[test]
fn t_slideex() {
    let goals = "(array (+ (* 6 (term_mvar n_0)) 6) (type_mvar t_1))=(array 18 f32)";
    let r = unify(goals).unwrap();
    assert_eq!(r, map![]);
}
#[test]
fn t_wtf() {
    let goals = "(array (+ 1 (+ (term_bvar n_0) 3)) (type_mvar t_1))=(array (term_mvar n_8) f32)";
    let r = unify(goals).unwrap();
    assert_eq!(r, map![]);
}
#[test]
fn t_wtf2() {
    let goals = "(array (term_mvar n_0) f32)=(array (* 3 (term_mvar p_10)) f32)";
    let r = unify(goals).unwrap();
    assert_eq!(r, map![]);
}

#[test]
fn distr() {
    let goals = "(term_mvar n_0)=(- (* 2 (+ 2 (/ (term_bvar w_0) 2))) 1)";
    // let goals = "(term_mvar n_0)=(* 2 (+ 2 (/ (term_bvar w_0) 2)))";
    // let goals = "(term_mvar n_0)=(+ 2 (/ (term_bvar w_0) 2))";
    // let goals = "(term_mvar n_0)=(* 2 (+ 2 (term_bvar w_0)))";
    let r = unify(goals).unwrap();
    pp(&r);
    assert_eq!(r, map![]);
}
#[test]
fn flow() {
    // let goals = "(term_mvar n_0)=(* 16 4)";
    let goals = "(term_mvar n_0)=(+ 1 (+ 2 (/ (term_bvar m_5) 2)))";
    // let goals = "(term_mvar n_0)=(* 2 (+ 2 (/ (term_bvar w_0) 2)))";
    // let goals = "(term_mvar n_0)=(+ 2 (/ (term_bvar w_0) 2))";
    // let goals = "(term_mvar n_0)=(* 2 (+ 2 (term_bvar w_0)))";
    let r = unify(goals).unwrap();
    pp(&r);
    assert_eq!(r, map![]);
}
#[test]
fn aplusc() {
    // let goals = "(term_mvar n_0)=(* 16 4)";
    let _goals = "(term_bvar n_0)=(+ (term_bvar m_5) 5)";
    let goals = "(+ 6 (term_bvar m_5))=(+ (term_bvar m_5) 5)";
    // let goals = "(term_mvar n_0)=(* 2 (+ 2 (/ (term_bvar w_0) 2)))";
    // let goals = "(term_mvar n_0)=(+ 2 (/ (term_bvar w_0) 2))";
    // let goals = "(term_mvar n_0)=(* 2 (+ 2 (term_bvar w_0)))";
    let r = unify(goals).unwrap();
    pp(&r);
    assert_eq!(r, map![]);
}

#[test]
fn abc() {
    // let goals = "(term_mvar n_0)=(* 16 4)";
    let goals = "(array (+ 5 (term_bvar x_1)) f32)=(array (+ (term_bvar x_1) (+ 3 2)) f32)";
    // let goals = "(term_mvar n_0)=(* 2 (+ 2 (/ (term_bvar w_0) 2)))";
    // let goals = "(term_mvar n_0)=(+ 2 (/ (term_bvar w_0) 2))";
    // let goals = "(term_mvar n_0)=(* 2 (+ 2 (term_bvar w_0)))";
    let r = unify(goals).unwrap();
    pp(&r);
    assert_eq!(r, map![]);
}

#[test]
fn def() {
    let goals = "(term_mvar n_0)=(/ (term_mvar p_1) (term_mvar n_0));";
    let r = unify(goals).unwrap();
    pp(&r);
    assert_eq!(r, map![]);
}

#[test]
fn scalqq() {
    let _goals = "(array (term_mvar n_0) (array (term_mvar m_1) (type_mvar t_2)))=(array (term_mvar n_3) (type_mvar t_5));(array (term_mvar n_3) (type_mvar s_4))=(array (term_mvar m_30) (array (* (* 4 128) 128) (type_mvar t_31)));(array (* (term_mvar m_30) (* (* 4 128) 128)) (type_mvar t_31))=(array (term_bvar n_0) f32);(-> (type_mvar s_4) (type_mvar t_5))=(-> (type_mvar anonymous_6) (array (* (term_mvar m_8) (term_mvar n_7)) (type_mvar t_9)));(array (term_mvar m_8) (vector (term_mvar n_7) (type_mvar t_9)))=(array (* (term_mvar n_11) (term_mvar m_12)) (type_mvar t_13));(type_mvar anonymous_10)=(type_mvar anonymous_6);(array (term_mvar n_11) (array (term_mvar m_12) (type_mvar t_13)))=(array (term_mvar n_15) (type_mvar t_17));(type_mvar anonymous_14)=(type_mvar anonymous_10);(array (term_mvar n_15) (type_mvar s_16))=(array (term_mvar m_26) (array 128 (type_mvar t_27)));(type_mvar anonymous_25)=(type_mvar anonymous_14);(array (* (term_mvar m_26) 128) (type_mvar t_27))=(array (term_mvar m_28) (vector 4 (type_mvar t_29)));(array (* (term_mvar m_28) 4) (type_mvar t_29))=(type_mvar anonymous_25);(-> (type_mvar s_16) (type_mvar t_17))=(-> (array(term_mvar n_18) (type_mvar s_19)) (array (term_mvar n_18) (type_mvar t_20)));(-> (type_mvar s_19) (type_mvar t_20))=(-> (type_mvar anonymous_21) (type_mvar t_22));(type_mvar t_22)=(vector (term_mvar n_23) (type_mvar t_24));(type_mvar t_24)=f32;(type_mvar t_22)=(type_mvar anonymous_21)";

    // let goals = "(array (term_mvar m_8) (vector (term_mvar n_7) (type_mvar t_9)))=(array (* (term_mvar n_11) (term_mvar m_12)) (type_mvar t_13));(array (term_mvar n_11) (array (term_mvar m_12) (type_mvar t_13)))=(array (term_mvar n_15) (type_mvar t_17));(array (term_mvar n_15) (type_mvar s_16))=(array (term_mvar m_26) (array 128 (type_mvar t_27)));(array (* (term_mvar m_26) 128) (type_mvar t_27))=(array (term_mvar m_28) (vector 4 (type_mvar t_29)))";
    let goals = "(array (* (term_mvar m_28) 4) (type_mvar t_29))=(type_mvar anonymous_25);(type_mvar anonymous_25)=(type_mvar anonymous_14);(type_mvar anonymous_14)=(type_mvar anonymous_10);(type_mvar anonymous_10)=(type_mvar anonymous_6);(-> (type_mvar s_4) (type_mvar t_5))=(-> (type_mvar anonymous_6) (array (* (term_mvar m_8) (term_mvar n_7)) (type_mvar t_9)));(array (term_mvar n_3) (type_mvar s_4))=(array (term_mvar m_30) (array (* (* 4 128) 128) (type_mvar t_31)))";

    let r = unify(goals).unwrap();
    pp(&r);
    assert_eq!(r, map![]);
}

// #[test]
// fn t_cle() {
//     let x = clean_divide(64, 4);
//     assert_eq!(x, Some(16));
//     let x = clean_divide(64, 3);
//     assert_eq!(x, None);
// }
// fn main() {
//     // simple_tests();
//     let _r = unify2(
//         "(-> (type_mvar a) (type_mvar b))",
//         "(-> (type_mvar c) (type_mvar c))",
//     );
//     // dbg!(r);
// }
