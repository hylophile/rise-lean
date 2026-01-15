use egg_unify::lang::unify;

use crate::common::*;

#[macro_use]
mod common;

#[test]
fn t_blub() {
    let r = unify2(
        "(array (nat_mvar n_1) (array (+ 1 (+ (nat_mvar n_5) (- (+ 2 (* 2 (/ (nat_bvar w_0) 2))) (nat_bvar w_0)))) (data_mvar t_8)))",
        "(array (nat_mvar n_10) (array (* (+ 1 (/ (- (+ (+ 1 (nat_mvar m_66)) 0) 2) 1)) 2) f32))")
    .unwrap();

    assert_eq!(r, map![("(nat_mvar a)", "1")]);
    // !(nat_mvar n_10)=(nat_mvar n_1);(data_mvar t_8)=f32
}

#[test]
fn t_lapl_upsamp() {
    let goals="(data_mvar anonymous_0)=(array (+ (/ (nat_bvar h_1) 2) 3) (array (+ (/ (nat_bvar w_0) 2) 3) f32));(array (nat_mvar n_1) (data_mvar s_2))=(array (nat_mvar n_10) (data_mvar d_11));(data_mvar anonymous_9)=(data_mvar anonymous_0);(array (+ (nat_mvar n_10) (- (+ 2 (* 2 (/ (nat_bvar h_1) 2))) (nat_bvar h_1))) (data_mvar d_11))=(array (nat_mvar m_13) (data_mvar t_14));(data_mvar anonymous_12)=(data_mvar anonymous_9);(array (+ 1 (nat_mvar m_13)) (data_mvar t_14))=(array (* (nat_mvar n_16) (nat_mvar m_17)) (data_mvar t_18));(data_mvar anonymous_15)=(data_mvar anonymous_12);(array (nat_mvar n_16) (array (nat_mvar m_17) (data_mvar t_18)))=(array (nat_mvar n_20) (data_mvar t_22));(data_mvar anonymous_19)=(data_mvar anonymous_15);(array (nat_mvar n_20) (data_mvar s_21))=(array (nat_mvar n_34) (data_mvar t_36));(data_mvar anonymous_33)=(data_mvar anonymous_19);(array (nat_mvar n_34) (data_mvar s_35))=(array (+ 1 (/ (- (nat_mvar n_60) 2) 1)) (array (+ 1 (/ (- (nat_mvar m_61) 2) 1)) (array 2 (array 2 (data_mvar d_62)))));(data_mvar anonymous_57)=(data_mvar anonymous_33);(array (nat_mvar n_60) (array (nat_mvar m_61) (data_mvar d_62)))=(array (+ (+ 1 (nat_mvar n_65)) 0) (array (+ (+ 1 (nat_mvar m_66)) 0) (data_mvar d_67)));(array (nat_mvar n_65) (array (nat_mvar m_66) (data_mvar d_67)))=(data_mvar anonymous_57);(-> (data_mvar s_35) (data_mvar t_36))=(-> (array (nat_mvar n_37) (data_mvar s_38)) (array (nat_mvar n_37) (data_mvar t_39)));(-> (data_mvar s_38) (data_mvar t_39))=(-> (data_mvar anonymous_40) (array (nat_mvar n_41) (data_mvar t_42)));(-> (index (nat_mvar n_41)) (data_mvar t_42))=(-> (index 2) (array (nat_mvar n_43) (data_mvar t_44)));(-> (index (nat_mvar n_43)) (data_mvar t_44))=(-> (index 2) f32);(data_mvar anonymous_45)=(data_mvar t_55);(data_mvar t_55)=(array 2 f32);(data_mvar t_55)=(array 2 f32);bool=bool;(data_mvar t_56)=(index 2);(data_mvar t_56)=(index 2);(data_mvar anonymous_46)=(data_mvar t_53);(data_mvar t_53)=(array 2 f32);(data_mvar t_53)=(array 2 f32);bool=bool;(data_mvar t_54)=(index 2);(data_mvar t_54)=(index 2);(data_mvar anonymous_47)=(data_mvar anonymous_40);(array (nat_mvar n_48) f32)=(array (nat_mvar n_49) (data_mvar t_51));(array (nat_mvar n_49) (data_mvar s_50))=(data_mvar anonymous_47);(-> (data_mvar s_50) (data_mvar t_51))=(-> (array (nat_mvar n_52) f32) f32);(array (nat_mvar n_52) f32)=(data_mvar anonymous_46);(array (nat_mvar n_48) f32)=(data_mvar anonymous_45);(-> (data_mvar s_21) (data_mvar t_22))=(-> (data_mvar anonymous_23) (array (nat_mvar n_24) (data_mvar t_26)));(array (nat_mvar n_24) (data_mvar s_25))=(array (nat_mvar m_31) (array (nat_mvar n_30) (data_mvar t_32)));(array (nat_mvar n_30) (array (nat_mvar m_31) (data_mvar t_32)))=(data_mvar anonymous_23);(-> (data_mvar s_25) (data_mvar t_26))=(-> (array (nat_mvar n_27) (array (nat_mvar m_28) (data_mvar t_29))) (array (* (nat_mvar n_27) (nat_mvar m_28)) (data_mvar t_29)));(-> (data_mvar s_2) (data_mvar t_3))=(-> (data_mvar anonymous_4) (array (nat_mvar n_5) (data_mvar d_6)));(array (+ (nat_mvar n_5) (- (+ 2 (* 2 (/ (nat_bvar w_0) 2))) (nat_bvar w_0))) (data_mvar d_6))=(array (nat_mvar m_7) (data_mvar t_8));(array (+ 1 (nat_mvar m_7)) (data_mvar t_8))=(data_mvar anonymous_4)";
    let r = unify(goals).unwrap();
    pp(&r);
    // assert_eq!(r, map![]);
    assert!(false);
}

#[test]
fn t_downsample() {
    let goals="(array (nat_mvar n_31) (array (nat_mvar m_32) f32))=(array (+ (nat_bvar h_1) 3) (array (+ (nat_bvar w_0) 3) f32));(array (nat_mvar n_1) (array (nat_mvar n_4) (array 4 (array 4 f32))))=(array (+ 1 (nat_mvar n_21)) (array (+ 1 (nat_mvar n_27)) (array 4 (array 4 (data_mvar d_33)))));(array (nat_mvar n_31) (array (nat_mvar m_32) (data_mvar d_33)))=(data_mvar anonymous_0);(array (nat_mvar n_14) (array (nat_mvar n_17) (array (nat_mvar m_18) (data_mvar t_19))))=(array (+ 1 (nat_mvar n_21)) (array 4 (array (+ 1 (nat_mvar n_27)) (array 4 (data_mvar d_33)))));(array (nat_mvar n_31) (array (nat_mvar m_32) (data_mvar d_33)))=(data_mvar anonymous_13);(array (+ (* 2 (nat_mvar n_21)) 4) (data_mvar t_22))=(array (+ (+ 1 (nat_mvar n_31)) (+ 2 (* 2 (- (+ 1 (/ (nat_bvar h_1) 2)) (/ (nat_bvar h_1) 2))))) (array (+ 1 (nat_mvar n_27)) (array 4 (data_mvar d_33))));(array (nat_mvar n_31) (array (nat_mvar m_32) (data_mvar d_33)))=(data_mvar anonymous_20);(array (nat_mvar n_24) (array (+ (* 2 (nat_mvar n_27)) 4) (data_mvar t_28)))=(array (+ (+ 1 (nat_mvar n_31)) (+ 2 (* 2 (- (+ 1 (/ (nat_bvar h_1) 2)) (/ (nat_bvar h_1) 2))))) (array (+ (+ 1 (nat_mvar m_32)) (+ 2 (* 2 (- (+ 1 (/ (nat_bvar w_0) 2)) (/ (nat_bvar w_0) 2))))) (data_mvar d_33)));(array (nat_mvar n_31) (array (nat_mvar m_32) (data_mvar d_33)))=(data_mvar anonymous_23);(-> (data_mvar s_25) (data_mvar t_26))=(-> (array (+ (* 2 (nat_mvar n_27)) 4) (data_mvar t_28)) (array (+ 1 (nat_mvar n_27)) (array 4 (data_mvar t_28))));(-> (data_mvar s_15) (data_mvar t_16))=(-> (array (nat_mvar n_17) (array (nat_mvar m_18) (data_mvar t_19))) (array (nat_mvar m_18) (array (nat_mvar n_17) (data_mvar t_19))));(-> (data_mvar s_2) (data_mvar t_3))=(-> (array (nat_mvar n_4) (array 4 (array 4 f32))) (array (nat_mvar n_4) f32));(-> (data_mvar s_5) (data_mvar t_6))=(-> (array 4 (array 4 f32)) f32);(array 4 f32)=(array (nat_mvar n_9) f32);(array (nat_mvar n_9) (array 4 f32))=(data_mvar anonymous_7);(-> (data_mvar s_10) (data_mvar t_11))=(-> (array 4 f32) f32);(array (nat_mvar n_12) f32)=(array 4 f32);(array (nat_mvar n_8) f32)=(array 4 f32)";
    // let goals="(array (nat_mvar n_31) (array (nat_mvar m_32) f32))=(array (+ (nat_bvar h_1) 3) (array (+ (nat_bvar w_0) 3) f32));(array (nat_mvar n_24) (array (+ (* 2 (nat_mvar n_27)) 4) (data_mvar t_28)))=(array (+ (+ 1 (nat_mvar n_31)) (+ 2 (* 2 (- (+ 1 (/ (nat_bvar h_1) 2)) (/ (nat_bvar h_1) 2))))) (array (+ (+ 1 (nat_mvar m_32)) (+ 2 (* 2 (- (+ 1 (/ (nat_bvar w_0) 2)) (/ (nat_bvar w_0) 2))))) (data_mvar d_33)))";
    let r = unify(goals).unwrap();
    pp(&r);
    assert_eq!(r, map![]);
}

#[test]
fn t_droplast() {
    let goals ="(array (+ (nat_bvar n_1) (nat_mvar m_0)) (data_mvar t_1))=(array (+ (nat_bvar n_1) (nat_bvar m_2)) (data_bvar d_0))";
    let r = unify(goals).unwrap();
    assert_eq!(r, map![]);
}

#[test]
fn t_scalintel() {
    let goals = "(array (nat_mvar n_0) (array (nat_mvar m_1) (data_mvar t_2)))=(array (nat_mvar n_3) (data_mvar t_5));(array (nat_mvar n_3) (data_mvar s_4))=(array (nat_mvar m_30) (array (* (* 4 128) 128) (data_mvar t_31)));(array (* (nat_mvar m_30) (* (* 4 128) 128)) (data_mvar t_31))=(array (nat_bvar n_0) f32);(-> (data_mvar s_4) (data_mvar t_5))=(-> (data_mvar anonymous_6) (array (* (nat_mvar m_8) (nat_mvar n_7)) (data_mvar t_9)));(array (nat_mvar m_8) (vector (nat_mvar n_7) (data_mvar t_9)))=(array (* (nat_mvar n_11) (nat_mvar m_12)) (data_mvar t_13));(data_mvar anonymous_10)=(data_mvar anonymous_6);(array (nat_mvar n_11) (array (nat_mvar m_12) (data_mvar t_13)))=(array (nat_mvar n_15) (data_mvar t_17));(data_mvar anonymous_14)=(data_mvar anonymous_10);(array (nat_mvar n_15) (data_mvar s_16))=(array (nat_mvar m_26) (array 128 (data_mvar t_27)));(data_mvar anonymous_25)=(data_mvar anonymous_14);(array (* (nat_mvar m_26) 128) (data_mvar t_27))=(array (nat_mvar m_28) (vector 4 (data_mvar t_29)));(array (* (nat_mvar m_28) 4) (data_mvar t_29))=(data_mvar anonymous_25);(-> (data_mvar s_16) (data_mvar t_17))=(-> (array (nat_mvar n_18) (data_mvar s_19)) (array (nat_mvar n_18) (data_mvar t_20)));(-> (data_mvar s_19) (data_mvar t_20))=(-> (data_mvar anonymous_21) (data_mvar t_22));(data_mvar t_22)=(vector (nat_mvar n_23) (data_mvar t_24));(data_mvar t_24)=f32;(data_mvar t_22)=(data_mvar anonymous_21)";
    let r = unify(goals).unwrap();
    // pp(&r);
    assert_eq!(r, map![]);
}
#[test]
fn t_scaliiintel_fail() {
    let goals = "(nat_mvar n_3)=(* (* 4 128) 128);(array (nat_mvar n_15) (data_mvar s_16))=(array (nat_mvar m_26) (array 128 (data_mvar t_27)));(-> (data_mvar s_16) (data_mvar t_17))=(-> (array (nat_mvar n_18) (data_mvar s_19)) (array (nat_mvar n_18) (data_mvar t_20)));";
    let r = unify(goals).unwrap();
    assert_eq!(r, map![]);
}

#[test]
fn t_padclamp2d() {
    let goals="(data_mvar anonymous_0)=(array (nat_bvar n_2) (array (nat_bvar m_1) (data_bvar d_0)));(array (nat_mvar n_1) (data_mvar t_2))=(array (nat_mvar n_3) (data_mvar t_5));(array (nat_mvar n_3) (data_mvar s_4))=(data_mvar anonymous_0);(-> (data_mvar s_4) (data_mvar t_5))=(-> (array (nat_mvar n_6) (data_mvar t_7)) (array (+ (+ (nat_bvar lInner_4) (nat_mvar n_6)) (nat_bvar rInner_3)) (data_mvar t_7)))";
    let r = unify(goals).unwrap();
    assert_eq!(r, map![]);
}

#[test]
fn t_simpslide2d4() {
    let goals="(data_mvar anonymous_0)=(array (nat_bvar n_2) (array (nat_bvar m_1) (data_bvar d_0)));(array (nat_mvar n_1) (data_mvar s_2))=(array (+ 1 (nat_mvar n_8)) (array (nat_bvar szOuter_6) (data_mvar t_9)));(data_mvar anonymous_7)=(data_mvar anonymous_0);(array (+ (* (nat_bvar stOuter_5) (nat_mvar n_8)) (nat_bvar szOuter_6)) (data_mvar t_9))=(array (nat_mvar n_10) (data_mvar t_12));(array (nat_mvar n_10) (data_mvar s_11))=(data_mvar anonymous_7)";
    let r = unify(goals).unwrap();
    assert_eq!(r, map![]);
}

#[test]
fn t_slide2d4() {
    let goals="(data_mvar anonymous_0)=(array (nat_bvar n_2) (array (nat_bvar m_1) (data_bvar d_0)));(array (nat_mvar n_1) (data_mvar s_2))=(array (+ 1 (nat_mvar n_8)) (array (nat_bvar szOuter_6) (data_mvar t_9)));(data_mvar anonymous_7)=(data_mvar anonymous_0);(array (+ (* (nat_bvar stOuter_5) (nat_mvar n_8)) (nat_bvar szOuter_6)) (data_mvar t_9))=(array (nat_mvar n_10) (data_mvar t_12));(array (nat_mvar n_10) (data_mvar s_11))=(data_mvar anonymous_7);(-> (data_mvar s_11) (data_mvar t_12))=(-> (array (+ (* (nat_bvar stInner_3) (nat_mvar n_13)) (nat_bvar szInner_4)) (data_mvar t_14)) (array (+ 1 (nat_mvar n_13)) (array (nat_bvar szInner_4) (data_mvar t_14))));(-> (data_mvar s_2) (data_mvar t_3))=(-> (array (nat_mvar n_4) (array (nat_mvar m_5) (data_mvar t_6))) (array (nat_mvar m_5) (array (nat_mvar n_4) (data_mvar t_6))))";
    let r = unify(goals).unwrap();
    assert_eq!(r, map![]);
}

#[test]
fn t_scalt() {
    //     let goals="(array (nat_mvar n_0) (array (nat_mvar m_1) (data_mvar t_2)))=(array (nat_mvar m_3) (array (* (* 4 128) 128) (data_mvar t_4)));(array (* (nat_mvar m_3) (* (* 4 128) 128)) (data_mvar t_4))=(array (nat_bvar n_0) f32)
    // ";
    let goals ="(array (nat_mvar n_0) (array (nat_mvar m_1) (data_mvar t_2)))=(array (nat_mvar m_3) (array 2 (data_mvar t_4)));(array (* (nat_mvar m_3) 2) (data_mvar t_4))=(array (nat_mvar m_5) (array (* (* 4 128) 128) (data_mvar t_6)));(array (* (nat_mvar m_5) (* (* 4 128) 128)) (data_mvar t_6))=(array (nat_bvar n_0) f32)";

    let r = unify(goals).unwrap();
    pp(&r);
    assert_eq!(r, map![]);
}

#[test]
fn t_slideex() {
    let goals = "(array (+ (* 6 (nat_mvar n_0)) 6) (data_mvar t_1))=(array 18 f32)";
    let r = unify(goals).unwrap();
    pp(&r);
    assert_eq!(r, map![]);
}

#[test]
fn t_wtf3() {
    // let goals = "(array (+ 1 (+ (nat_bvar n_0) 3)) (data_mvar t_1))=(array (nat_mvar n_8) f32)";
    let goals = "(nat_mvar n_1)  = (+ (- (+ (nat_bvar h_1) 6) 1) -2)";
    let r = unify(goals).unwrap();
    assert_eq!(r, map![]);
}

#[test]
fn t_wtf2() {
    let goals = "(array (nat_mvar n_0) f32)=(array (* 3 (nat_mvar p_10)) f32)";
    let r = unify(goals).unwrap();
    assert_eq!(r, map![]);
}

#[test]
fn distr() {
    let goals = "(nat_mvar n_0)=(- (* 2 (+ 2 (/ (nat_bvar w_0) 2))) 1)";
    // let goals = "(nat_mvar n_0)=(* 2 (+ 2 (/ (nat_bvar w_0) 2)))";
    // let goals = "(nat_mvar n_0)=(+ 2 (/ (nat_bvar w_0) 2))";
    // let goals = "(nat_mvar n_0)=(* 2 (+ 2 (nat_bvar w_0)))";
    let r = unify(goals).unwrap();
    pp(&r);
    assert_eq!(r, map![]);
}

#[test]
fn flow() {
    // let goals = "(nat_mvar n_0)=(* 16 4)";
    let goals = "(nat_mvar n_0)=(+ 1 (+ 2 (/ (nat_bvar m_5) 2)))";
    // let goals = "(nat_mvar n_0)=(* 2 (+ 2 (/ (nat_bvar w_0) 2)))";
    // let goals = "(nat_mvar n_0)=(+ 2 (/ (nat_bvar w_0) 2))";
    // let goals = "(nat_mvar n_0)=(* 2 (+ 2 (nat_bvar w_0)))";
    let r = unify(goals).unwrap();
    pp(&r);
    assert_eq!(r, map![]);
}

#[test]
fn aplusc() {
    // let goals = "(nat_mvar n_0)=(* 16 4)";
    let _goals = "(nat_bvar n_0)=(+ (nat_bvar m_5) 5)";
    let goals = "(+ 6 (nat_bvar m_5))=(+ (nat_bvar m_5) 5)";
    // let goals = "(nat_mvar n_0)=(* 2 (+ 2 (/ (nat_bvar w_0) 2)))";
    // let goals = "(nat_mvar n_0)=(+ 2 (/ (nat_bvar w_0) 2))";
    // let goals = "(nat_mvar n_0)=(* 2 (+ 2 (nat_bvar w_0)))";
    let r = unify(goals).unwrap();
    pp(&r);
    assert_eq!(r, map![]);
}

#[test]
fn abc() {
    // let goals = "(nat_mvar n_0)=(* 16 4)";
    let goals = "(array (+ 5 (nat_bvar x_1)) f32)=(array (+ (nat_bvar x_1) (+ 3 2)) f32)";
    // let goals = "(nat_mvar n_0)=(* 2 (+ 2 (/ (nat_bvar w_0) 2)))";
    // let goals = "(nat_mvar n_0)=(+ 2 (/ (nat_bvar w_0) 2))";
    // let goals = "(nat_mvar n_0)=(* 2 (+ 2 (nat_bvar w_0)))";
    let r = unify(goals).unwrap();
    pp(&r);
    assert_eq!(r, map![]);
}

#[test]
fn def() {
    let goals = "(nat_mvar n_0)=(/ (nat_mvar p_1) (nat_mvar n_0));";
    let r = unify(goals).unwrap();
    pp(&r);
    assert_eq!(r, map![]);
}
#[test]
fn unsound() {
    let goals = "(nat_mvar n_0)=(+ (+ 5 5) -10);(nat_mvar m_1)=0;(nat_mvar p_2)=(/ (nat_bvar h_5) (nat_mvar m_1))";
    let goals = "(nat_mvar n_0)=(* (nat_mvar m_2) (nat_mvar p_3));(nat_mvar n_0)=2;(nat_mvar)";
    let r = unify(goals).unwrap();
    pp(&r);
    assert_eq!(r, map![]);
}

#[test]
fn scalqq() {
    let _goals = "(array (nat_mvar n_0) (array (nat_mvar m_1) (data_mvar t_2)))=(array (nat_mvar n_3) (data_mvar t_5));(array (nat_mvar n_3) (data_mvar s_4))=(array (nat_mvar m_30) (array (* (* 4 128) 128) (data_mvar t_31)));(array (* (nat_mvar m_30) (* (* 4 128) 128)) (data_mvar t_31))=(array (nat_bvar n_0) f32);(-> (data_mvar s_4) (data_mvar t_5))=(-> (data_mvar anonymous_6) (array (* (nat_mvar m_8) (nat_mvar n_7)) (data_mvar t_9)));(array (nat_mvar m_8) (vector (nat_mvar n_7) (data_mvar t_9)))=(array (* (nat_mvar n_11) (nat_mvar m_12)) (data_mvar t_13));(data_mvar anonymous_10)=(data_mvar anonymous_6);(array (nat_mvar n_11) (array (nat_mvar m_12) (data_mvar t_13)))=(array (nat_mvar n_15) (data_mvar t_17));(data_mvar anonymous_14)=(data_mvar anonymous_10);(array (nat_mvar n_15) (data_mvar s_16))=(array (nat_mvar m_26) (array 128 (data_mvar t_27)));(data_mvar anonymous_25)=(data_mvar anonymous_14);(array (* (nat_mvar m_26) 128) (data_mvar t_27))=(array (nat_mvar m_28) (vector 4 (data_mvar t_29)));(array (* (nat_mvar m_28) 4) (data_mvar t_29))=(data_mvar anonymous_25);(-> (data_mvar s_16) (data_mvar t_17))=(-> (array(nat_mvar n_18) (data_mvar s_19)) (array (nat_mvar n_18) (data_mvar t_20)));(-> (data_mvar s_19) (data_mvar t_20))=(-> (data_mvar anonymous_21) (data_mvar t_22));(data_mvar t_22)=(vector (nat_mvar n_23) (data_mvar t_24));(data_mvar t_24)=f32;(data_mvar t_22)=(data_mvar anonymous_21)";

    // let goals = "(array (nat_mvar m_8) (vector (nat_mvar n_7) (data_mvar t_9)))=(array (* (nat_mvar n_11) (nat_mvar m_12)) (data_mvar t_13));(array (nat_mvar n_11) (array (nat_mvar m_12) (data_mvar t_13)))=(array (nat_mvar n_15) (data_mvar t_17));(array (nat_mvar n_15) (data_mvar s_16))=(array (nat_mvar m_26) (array 128 (data_mvar t_27)));(array (* (nat_mvar m_26) 128) (data_mvar t_27))=(array (nat_mvar m_28) (vector 4 (data_mvar t_29)))";
    let goals = "(array (* (nat_mvar m_28) 4) (data_mvar t_29))=(data_mvar anonymous_25);(data_mvar anonymous_25)=(data_mvar anonymous_14);(data_mvar anonymous_14)=(data_mvar anonymous_10);(data_mvar anonymous_10)=(data_mvar anonymous_6);(-> (data_mvar s_4) (data_mvar t_5))=(-> (data_mvar anonymous_6) (array (* (nat_mvar m_8) (nat_mvar n_7)) (data_mvar t_9)));(array (nat_mvar n_3) (data_mvar s_4))=(array (nat_mvar m_30) (array (* (* 4 128) 128) (data_mvar t_31)))";

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
//         "(-> (data_mvar a) (data_mvar b))",
//         "(-> (data_mvar c) (data_mvar c))",
//     );
//     // dbg!(r);
// }
