use egg::*;
use std::ffi::{c_char, CStr, CString};

define_language! {
    enum RiseType {
        "array" = Array([Id; 2]),
        "pair" = Pair([Id; 2]),
        "index" = Index([Id; 1]),
        "vector" = Vector([Id; 2]),
        "→" = Fn([Id; 2]),
        Num(i32),
        "+" = Add([Id; 2]),
        "*" = Mul([Id; 2]),
        "~" = Unify([Id; 2]),
        // "int" = Int,
        "mvar" = MVar(Id),
        Symbol(Symbol),
    }
}

#[rustfmt::skip]
fn rules() -> Vec<Rewrite<RiseType, ()>> {
    vec![
        rewrite!("commute-add"; "(+ ?a ?b)" => "(+ ?b ?a)"),
        rewrite!("commute-mul"; "(* ?a ?b)" => "(* ?b ?a)"),
        rewrite!("commute-unify"; "(~ ?a ?b)" => "(~ ?b ?a)"),

        rewrite!("add-0"; "(+ ?a 0)" => "?a"),
        rewrite!("mul-0"; "(* ?a 0)" => "0"),
        rewrite!("mul-1"; "(* ?a 1)" => "?a"),

        multi_rewrite!("10"; "?v = (~ (array ?n1 ?d1) (array ?n2 ?d2))"             => "?v = (~ ?n1 ?n2) = (~ ?d1 ?d2)"),
        multi_rewrite!("12"; "?v = (~ (array ?t1 ?t2) (mvar ?c))"                   => "?w = (array ?t1 ?t2) = (mvar ?c)"),

        multi_rewrite!("11"; "?v = (~ (pair ?n1 ?d1) (pair ?n2 ?d2))"               => "?v = (~ ?n1 ?n2) = (~ ?d1 ?d2)"),
        multi_rewrite!("13"; "?v = (~ (pair ?t1 ?t2) (mvar ?c))"                    => "?w = (pair ?t1 ?t2) = (mvar ?c)"),

        multi_rewrite!("40"; "?v = (~ (→ ?t1 ?t3) (→ ?t2 ?t4))"                   => "?v = (~ ?t1 ?t2) = (~ ?t3 ?t4)"),

        multi_rewrite!("41"; "?v = (~ (+ (mvar ?n1) ?t3) (+ (mvar ?n2) ?t4))"       => "?w = (mvar ?n1) = (mvar ?n2)"),
        multi_rewrite!("42"; "?v = (~ (* (mvar ?n1) ?t3) (* (mvar ?n2) ?t4))"       => "?w = (mvar ?n1) = (mvar ?n2)"),

        multi_rewrite!("32"; "?v = (~ (mvar ?a) (mvar ?b))"                         => "?w = (mvar ?a) = (mvar ?b)"),
        multi_rewrite!("30"; "?v = (~ int (mvar ?b))"                               => "?w = int = (mvar ?b)"),
        multi_rewrite!("31"; "?v = (~ bool (mvar ?b))"                              => "?w = bool = (mvar ?b)"),
    ]
}

// fn unify(s1: &str, s2: &str) {
//     let u: RecExpr<RiseType> = format!("(~ {s1} {s2})").parse().unwrap();
//     let mut eg: EGraph<RiseType, ()> = EGraph::new(());
//     eg.add_expr(&u);
//     let runner = Runner::default().with_egraph(eg).run(&rules());
//     // runner.egraph.dot().to_svg("target/foo.svg").unwrap();
// }

// fn simple_tests() {
//     // thesis: if for every ~-enode, both edges point to the same eclass, unification is successful.

//     // unify("(array (+ (mvar n1) 2) int)", "(array (+ 2 (mvar n2)) int)");
//     // unify("(array (+ (mvar n1) 2) int)", "(array (+ 3 (mvar n2)) int)");
//     // unify("(array (mvar n1) int)", "(array (mvar n2) int)");
//     // unify("(→ (mvar a) (mvar b))", "(→ (mvar c) (mvar c))");
//     unify("(→ int (mvar b))", "(→ f32 (mvar c))");
//     // unify("(→ int (mvar b))", "(→ bool (mvar c))");
//     // unify("(→ int (mvar b))", "(→ int (mvar c))");
//     // unify("(→ (mvar a) (mvar b))", "(→ (mvar b) (mvar a))");
//     // unify(
//     //     "(→ (pair (mvar a) (mvar b)) (mvar c))",
//     //     "(→ (mvar c) (mvar d))",
//     // );
//     // unify("(pair (mvar a) (mvar b))", "(mvar c)");
//     // unify(
//     //     "(→ (mvar a) (→ (mvar b) (mvar b)))",
//     //     "(→ (mvar c) (→ (mvar a) (mvar a)))",
//     // );
//     // unify("(→ (mvar a) (mvar b))", "(→ (mvar a) (mvar c))");
//     // unify("(mvar a)", "(array 3 (mvar a))");
// }

// fn main() {
//     simple_tests();
// }

// Cf. https://doc.rust-lang.org/stable/std/ffi/struct.CStr.html#examples
fn c_str_to_string(c_str: *const c_char) -> String {
    let str = unsafe { CStr::from_ptr(c_str) };
    String::from_utf8_lossy(str.to_bytes()).to_string()
}

// TODO: I think this is a memory leak right now.
fn string_to_c_str(str: String) -> *const c_char {
    let expl_c_str = CString::new(str).expect("conversion of Rust-string to C-string failed");

    expl_c_str.into_raw()
}

#[no_mangle]
pub extern "C" fn run_egg(input: *const c_char) -> *const c_char {
    let input = c_str_to_string(input);

    let u: RecExpr<RiseType> = input.parse().unwrap();
    let mut eg: EGraph<RiseType, ()> = EGraph::new(());
    eg.add_expr(&u);
    let runner = Runner::default().with_egraph(eg).run(&rules());
    // runner.egraph.dot().to_svg("target/foo.svg").unwrap();

    let res: String = format!("{:?}", runner.egraph.dump());
    // next steps:
    // - check that the unify eclass only has [x,x] nodes and no [x,y] nodes
    // - find the mvar class(es)
    // - find the "most concrete terms" and generate substitution
    // - stringify substitution, return it, and parse it with lean.
    string_to_c_str(res)
}
