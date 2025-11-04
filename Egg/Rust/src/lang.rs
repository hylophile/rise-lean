use egg::*;
use std::collections::HashMap;
use std::time::Duration;

define_language! {
    pub enum RiseType {
        "array" = Array([Id; 2]),
        "vector" = Vector([Id; 2]),
        "pair" = Pair([Id; 2]),
        "index" = Index(Id),
        "->" = Fn([Id; 2]),
        Num(i32),
        "+" = Add([Id; 2]),
        "*" = Mul([Id; 2]),
        "/" = Div([Id; 2]),
        "-" = Sub([Id; 2]),
        // "~" = Unify([Id; 2]),
        // "int" = Int,
        "type_mvar" = TypeMVar(Id),
        "type_bvar" = TypeBVar(Id),
        "term_mvar" = TermMVar(Id),
        "term_bvar" = TermBVar(Id),
        Symbol(Symbol),
    }
}

use rand::distr::Alphanumeric;
use rand::{rng, Rng};

fn s() -> String {
    let rand_string: String = rng()
        .sample_iter(&Alphanumeric)
        .take(5)
        .map(char::from)
        .collect();
    rand_string
}

#[rustfmt::skip]
fn rules() -> Vec<Rewrite<RiseType, UnifyAnalysis>> {
    vec![
        rewrite!("commute-add"; "(+ ?a ?b)" => "(+ ?b ?a)"),
        rewrite!("commute-mul"; "(* ?a ?b)" => "(* ?b ?a)"),
        // rewrite!("commute-unify"; "(~ ?a ?b)" => "(~ ?b ?a)"),

        rewrite!(s(); "(+ ?a 0)" => "?a"),
        rewrite!(s(); "(* ?a 0)" => "0"),
        rewrite!(s(); "(* ?a 1)" => "?a"),

        // multi_rewrite!(s(); "?v = (+ ?a ?b) = ?a" => "?a = 888"),
        // todo: how do we detect positive/negative inf?

        // multi_rewrite!(s(); "?v = (+ ?a ?b) = (+ ?c ?d)" => "?a = ?c, ?b = ?d"),
        // multi_rewrite!(s(); "?v = (* ?a ?b) = (* ?c ?d)" => "?a = ?c, ?b = ?d"),
        multi_rewrite!(s(); "?v = (-> ?a ?b) = (-> ?c ?d)" => "?a = ?c, ?b = ?d"),
        multi_rewrite!(s(); "?v = (array ?a ?b) = (array ?c ?d)" => "?a = ?c, ?b = ?d"),
        multi_rewrite!(s(); "?v = (vector ?a ?b) = (vector ?c ?d)" => "?a = ?c, ?b = ?d"),
        multi_rewrite!(s(); "?v = (pair ?a ?b) = (pair ?c ?d)" => "?a = ?c, ?b = ?d"),
        multi_rewrite!(s(); "?v = (index ?a) = (index ?c)" => "?a = ?c"),

        // multi_rewrite!(s(); "?v = (~ (array ?n1 ?d1) (array ?n2 ?d2))"             => "?v = (~ ?n1 ?n2) = (~ ?d1 ?d2)"),
        // multi_rewrite!(s(); "?v = (~ (array ?t1 ?t2) (type_mvar )?c))"                   => "?w = (array ?t1 ?t2) = (type_mvar )?c)"),

        // multi_rewrite!(s(); "?v = (~ (pair ?n1 ?d1) (pair ?n2 ?d2))"               => "?v = (~ ?n1 ?n2) = (~ ?d1 ?d2)"),
        // multi_rewrite!(s(); "?v = (~ (pair ?t1 ?t2) (type_mvar )?c))"                    => "?w = (pair ?t1 ?t2) = (type_mvar )?c)"),

        // multi_rewrite!(s(); "?v = (~ (-> ?t1 ?t3) (-> ?t2 ?t4))"                   => "?v = (~ ?t1 ?t2) = (~ ?t3 ?t4)"),

        // multi_rewrite!(s(); "?v = (~ (+ (type_mvar )?n1) ?t3) (+ (type_mvar )?n2) ?t4))"       => "?w = (type_mvar )?n1) = (type_mvar )?n2)"),
        // multi_rewrite!(s(); "?v = (~ (* (type_mvar )?n1) ?t3) (* (type_mvar )?n2) ?t4))"       => "?w = (type_mvar )?n1) = (type_mvar )?n2)"),

        // multi_rewrite!(s(); "?v = (~ (type_mvar )?a) (type_mvar )?b))"                         => "?w = (type_mvar )?a) = (type_mvar )?b)"),
        // multi_rewrite!(s(); "?v = (~ int (type_mvar )?b))"                               => "?w = int = (type_mvar )?b)"),
        // multi_rewrite!(s(); "?v = (~ bool (type_mvar )?b))"                              => "?w = bool = (type_mvar )?b)"),
    ]
}

#[derive(Debug, Clone)]
struct UnifyAnalysis {
    value: Result<(), String>,
}

impl Default for UnifyAnalysis {
    fn default() -> Self {
        Self { value: Ok(()) }
    }
}

fn check_no_self_loops(
    egraph: &EGraph<RiseType, UnifyAnalysis>,
    class: &EClass<RiseType, Variant>,
) -> Result<(), String> {
    let id = class.id;
    for enode in &class.nodes {
        if get_variant(enode) == Variant::Term {
            continue;
        }
        for &child_id in enode.children() {
            let child_root = egraph.find(child_id);
            if child_root == id {
                return Err(format!(
                    "occurs check failed: enode {:?} in eclass {:?} points to its own class",
                    enode, id
                ));
            }
        }
    }
    Ok(())
}

#[derive(Debug, Clone, PartialEq, Eq)]
enum Variant {
    Term,
    TermMVar,
    TypeMVar,
    TypeName(String),
}
fn get_variant(i: &RiseType) -> Variant {
    match i {
        RiseType::TermBVar(_)
        | RiseType::Num(_)
        | RiseType::Add(_)
        | RiseType::Mul(_)
        | RiseType::Div(_)
        | RiseType::Sub(_) => Variant::Term,
        RiseType::TypeMVar(_) => Variant::TypeMVar,
        RiseType::TermMVar(_) => Variant::TermMVar,
        RiseType::Symbol(s) => Variant::TypeName(s.to_string()),
        RiseType::TypeBVar(_) => Variant::TypeName("bvar".to_string()),
        RiseType::Array(_) => Variant::TypeName("array".to_string()),
        RiseType::Vector(_) => Variant::TypeName("array".to_string()),
        RiseType::Pair(_) => Variant::TypeName("pair".to_string()),
        RiseType::Index(_) => Variant::TypeName("index".to_string()),
        RiseType::Fn(_) => Variant::TypeName("fn".to_string()),
    }
}

impl Analysis<RiseType> for UnifyAnalysis {
    type Data = Variant;

    fn make(_egraph: &mut EGraph<RiseType, Self>, enode: &RiseType) -> Self::Data {
        get_variant(enode)
    }

    fn merge(&mut self, a: &mut Self::Data, b: Self::Data) -> DidMerge {
        use Variant::*;
        let (new_val, a_changed, b_changed) = match (a.clone(), b.clone()) {
            (v @ Term, Term) | (v @ TermMVar, TermMVar) | (v @ TypeMVar, TypeMVar) => {
                (v, false, false)
            }

            (Term, TermMVar) => (Term, false, true),
            (TermMVar, Term) => (Term, true, false),

            (TypeName(s), TypeMVar) => (TypeName(s), false, true),
            (TypeMVar, TypeName(s)) => (TypeName(s), true, false),

            (TypeName(s1), TypeName(s2)) => {
                if s1 == s2 {
                    (TypeName(s1.clone()), false, false)
                } else {
                    self.value = Err(format!("merge conflict: {a:?} {b:?}"));
                    (TypeName(s1.clone()), false, false)
                }
            }

            (_, v) => {
                self.value = Err(format!("merge conflict: {a:?} {b:?}"));
                (v, false, false)
            }
        };
        *a = new_val;
        DidMerge(a_changed, b_changed)
    }
}

// #[derive(PartialEq, Eq, PartialOrd, Debug, Clone, Copy)]
// struct MCost {
//     mvars: usize,
//     rest: usize,
// }

// impl Ord for MCost {
//     fn cmp(&self, other: &Self) -> std::cmp::Ordering {
//         use std::cmp::Ordering::*;
//         match self.mvars.cmp(&other.mvars) {
//             Less => todo!(),
//             Equal => todo!(),
//             Greater => todo!(),
//         }
//     }
// }

// struct UnifyCostFn;
// impl CostFunction<RiseType> for UnifyCostFn {
//     type Cost = usize;
//     fn cost<C>(&mut self, enode: &RiseType, mut costs: C) -> Self::Cost
//     where
//         C: FnMut(Id) -> Self::Cost,
//     {
//         match enode {
//             RiseType::TermMVar(_) | RiseType::TypeMVar(_) => return 100,
//             _ => 1 + (enode.fold(0, |sum: usize, id| sum.saturating_add(costs(id))) / 10),
//         }
//     }
// }

fn is_mvar(l: &RiseType) -> bool {
    match l {
        RiseType::TermMVar(_) | RiseType::TypeMVar(_) => true,
        _ => false,
    }
}

fn pretty_mvar(egraph: &EGraph<RiseType, UnifyAnalysis>, l: &RiseType) -> Option<String> {
    let prefix = match l {
        RiseType::TermMVar(_) => Some("term_"),
        RiseType::TypeMVar(_) => Some("type_"),
        _ => None,
    }?;
    let x = l.children().get(0)?;
    match egraph[*x].nodes.get(0)? {
        RiseType::Symbol(s) => Some(format!("({prefix}mvar {s})")),
        _ => None,
    }
}

fn unify2(s1: &str, s2: &str) -> Result<HashMap<String, String>, String> {
    unify(&format!("{s1}={s2}"))
}

pub fn unify(input: &str) -> Result<HashMap<String, String>, String> {
    let goals: Vec<(&str, &str)> = input
        .split(';')
        .map(|x| x.split_once('=').ok_or(format!("invalid input: {input}")))
        .collect::<Result<Vec<(&str, &str)>, String>>()?;

    // setup
    let mut eg: EGraph<RiseType, UnifyAnalysis> = EGraph::new(UnifyAnalysis::default());
    for (s1, s2) in goals {
        let a: RecExpr<RiseType> = s1.parse().unwrap();
        let b: RecExpr<RiseType> = s2.parse().unwrap();
        let id_a = eg.add_expr(&a);
        let id_b = eg.add_expr(&b);
        eg.union(id_a, id_b);
    }

    // run
    let runner: Runner<RiseType, UnifyAnalysis> = Runner::default()
        .with_egraph(eg)
        .with_time_limit(Duration::from_secs(1))
        .run(&rules());
    #[cfg(test)]
    runner.egraph.dot().to_svg("target/foo.svg").unwrap();

    for class in runner.egraph.classes() {
        check_no_self_loops(&runner.egraph, class)?
    }

    let _ = runner.egraph.analysis.value.clone()?;

    let mut map = HashMap::new();
    let mut reprs = HashMap::new();
    // find reprs
    for class in runner.egraph.classes() {
        let (mvars, rest): (Vec<&RiseType>, Vec<&RiseType>) =
            class.nodes.iter().partition(|n| is_mvar(*n));
        match rest.len() {
            0 => {
                reprs.insert(class.id, *mvars.iter().min().unwrap());
                continue;
            }
            1.. => {
                // let repr = *rest.get(0).unwrap();
                let repr = *rest.iter().min().unwrap();
                if repr.children().iter().any(|i| *i == class.id) {
                    reprs.insert(class.id, *mvars.iter().min().unwrap());
                    continue;
                } else {
                    reprs.insert(class.id, repr);
                    continue;
                }
            }
        }
        // if class.nodes.iter().any(|x| is_mvar(x)) {
        //     let (_cost, x) = extractor.find_best(class.id);
        //     class.nodes.iter().for_each(|n| {
        //         if is_mvar(n) {
        //             dbg!(_cost, &x);
        //             if let Some(p) = pretty_mvar(&runner.egraph, n) {
        //                 // dbg!(_cost, &x, &p);
        //                 let x = x.pretty(1000);
        //                 if x != p {
        //                     map.insert(p, x);
        //                 }
        //             }
        //         }
        //     });
        // }
    }
    for class in runner.egraph.classes() {
        class.nodes.iter().filter(|n| is_mvar(*n)).for_each(|n| {
            let repr = reprs
                .get(&class.id)
                .unwrap()
                .build_recexpr(|id| (*reprs.get(&id).unwrap()).clone());
            if let Some(p) = pretty_mvar(&runner.egraph, n) {
                let repr = repr.pretty(1000);
                if repr != p {
                    map.insert(p, repr);
                }
            }
        });
    }
    // dbg!(reprs);
    Ok(map)
}

#[cfg(test)]
macro_rules! map {
    ( $( ( $key:expr, $val:expr ) ),* $(,)? ) => {{
        #[allow(unused_mut)]
        let mut map = std::collections::HashMap::<String, String>::new();
        $(
            map.insert($key.to_string(), $val.to_string());
        )*
        map
    }};
}

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
    let r = unify2("(term_mvar a)", "(+ 1 (term_mvar a))").unwrap();
    assert_eq!(r, map![("(term_mvar a)", "1")]);
}

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
fn t_a() {
    let goals = "(array (term_mvar n_65) (array (term_mvar m_66) f32))=(array (+ (/ (term_bvar h_1) 2) 3) (array (+ (/ (term_bvar w_0) 2) 3) f32));(array (term_mvar n_1) (array (+ 1 (+ (term_mvar n_5) (- (+ 2 (* 2 (/ (term_bvar w_0) 2))) (term_bvar w_0)))) (type_mvar t_8)))=(array (term_mvar n_10) (array (* (+ 1 (/ (- (+ (+ 1 (term_mvar m_66)) 0) 2) 1)) 2) f32));(array (term_mvar n_65) (array (term_mvar m_66) f32))=(type_mvar [anonymous]_0);(array (+ (term_mvar n_10) (- (+ 2 (* 2 (/ (term_bvar h_1) 2))) (term_bvar h_1))) (type_mvar d_11))=(array (term_mvar m_13) (array (* (+ 1 (/ (- (+ (+ 1 (term_mvar m_66)) 0) 2) 1)) 2) f32));(array (term_mvar n_65) (array (term_mvar m_66) f32))=(type_mvar [anonymous]_9);(array (+ 1 (term_mvar m_13)) (type_mvar t_14))=(array (* (+ 1 (/ (- (+ (+ 1 (term_mvar n_65)) 0) 2) 1)) 2) (array (* (+ 1 (/ (- (+ (+ 1 (term_mvar m_66)) 0) 2) 1)) 2) f32));(array (term_mvar n_65) (array (term_mvar m_66) f32))=(type_mvar [anonymous]_12);(array (term_mvar n_16) (array (term_mvar m_17) (type_mvar t_18)))=(array (+ 1 (/ (- (+ (+ 1 (term_mvar n_65)) 0) 2) 1)) (array 2 (array (* (+ 1 (/ (- (+ (+ 1 (term_mvar m_66)) 0) 2) 1)) 2) f32)));(array (term_mvar n_65) (array (term_mvar m_66) f32))=(type_mvar [anonymous]_15);(array (term_mvar n_20) (array (term_mvar n_30) (array (term_mvar m_31) (array (term_mvar m_28) (type_mvar t_29)))))=(array (+ 1 (/ (- (+ (+ 1 (term_mvar n_65)) 0) 2) 1)) (array (+ 1 (/ (- (+ (+ 1 (term_mvar m_66)) 0) 2) 1)) (array 2 (array 2 f32))));(array (term_mvar n_65) (array (term_mvar m_66) f32))=(type_mvar [anonymous]_19);(array (term_mvar n_34) (array (term_mvar n_37) (array 2 (array 2 f32))))=(array (+ 1 (/ (- (+ (+ 1 (term_mvar n_65)) 0) 2) 1)) (array (+ 1 (/ (- (+ (+ 1 (term_mvar m_66)) 0) 2) 1)) (array 2 (array 2 (type_mvar d_67)))));(array (term_mvar n_65) (array (term_mvar m_66) (type_mvar d_67)))=(type_mvar [anonymous]_33);(array (term_mvar n_60) (array (term_mvar m_61) (type_mvar d_62)))=(array (+ (+ 1 (term_mvar n_65)) 0) (array (+ (+ 1 (term_mvar m_66)) 0) (type_mvar d_67)));(array (term_mvar n_65) (array (term_mvar m_66) (type_mvar d_67)))=(type_mvar [anonymous]_57);(-> (type_mvar s_35) (type_mvar t_36))=(-> (array (term_mvar n_37) (array 2 (array 2 f32))) (array (term_mvar n_37) (array 2 (array 2 f32))));(-> (type_mvar s_38) (type_mvar t_39))=(-> (array 2 (array 2 f32)) (array 2 (array 2 f32)));(-> (index (term_mvar n_41)) (type_mvar t_42))=(-> (index 2) (array 2 f32));(-> (index (term_mvar n_43)) (type_mvar t_44))=(-> (index 2) f32);(array (term_mvar n_49) f32)=(array 2 f32);(array 2 f32)=(array 2 f32);(type_mvar t_55)=(array 2 f32);bool=bool;(index 2)=(index 2);(type_mvar t_56)=(index 2);(array (term_mvar n_52) f32)=(array 2 f32);(array 2 f32)=(array 2 f32);(type_mvar t_53)=(array 2 f32);bool=bool;(index 2)=(index 2);(type_mvar t_54)=(index 2);(array (term_mvar n_49) (array (term_mvar n_52) f32))=(type_mvar [anonymous]_40);(array (term_mvar n_48) f32)=(array (term_mvar n_49) f32);(array (term_mvar n_49) (array (term_mvar n_52) f32))=(type_mvar [anonymous]_47);(-> (type_mvar s_50) (type_mvar t_51))=(-> (array (term_mvar n_52) f32) f32);(array (term_mvar n_52) f32)=(type_mvar [anonymous]_46);(array (term_mvar n_48) f32)=(type_mvar [anonymous]_45);(-> (type_mvar s_21) (type_mvar t_22))=(-> (array (term_mvar n_30) (array (term_mvar m_31) (array (term_mvar m_28) (type_mvar t_29)))) (array (term_mvar m_31) (array (* (term_mvar n_30) (term_mvar m_28)) (type_mvar t_29))));(array (term_mvar n_24) (array (term_mvar n_27) (array (term_mvar m_28) (type_mvar t_29))))=(array (term_mvar m_31) (array (term_mvar n_30) (type_mvar t_32)));(array (term_mvar n_30) (array (term_mvar m_31) (type_mvar t_32)))=(type_mvar [anonymous]_23);(-> (type_mvar s_25) (type_mvar t_26))=(-> (array (term_mvar n_27) (array (term_mvar m_28) (type_mvar t_29))) (array (* (term_mvar n_27) (term_mvar m_28)) (type_mvar t_29)));(-> (type_mvar s_2) (type_mvar t_3))=(-> (array (+ 1 (+ (term_mvar n_5) (- (+ 2 (* 2 (/ (term_bvar w_0) 2))) (term_bvar w_0)))) (type_mvar t_8)) (array (term_mvar n_5) (type_mvar t_8)));(array (+ (term_mvar n_5) (- (+ 2 (* 2 (/ (term_bvar w_0) 2))) (term_bvar w_0))) (type_mvar d_6))=(array (term_mvar m_7) (type_mvar t_8));(array (+ 1 (term_mvar m_7)) (type_mvar t_8))=(type_mvar [anonymous]_4)";
    let r = unify(goals).unwrap();
    assert_eq!(r, map![]);
}

#[test]
fn t_downsample() {
    let goals="(array (term_mvar n_31) (array (term_mvar m_32) f32))=(array (+ (term_bvar h_1) 3) (array (+ (term_bvar w_0) 3) f32));(array (term_mvar n_1) (array (term_mvar n_4) (array 4 (array 4 f32))))=(array (+ 1 (term_mvar n_21)) (array (+ 1 (term_mvar n_27)) (array 4 (array 4 (type_mvar d_33)))));(array (term_mvar n_31) (array (term_mvar m_32) (type_mvar d_33)))=(type_mvar anonymous_0);(array (term_mvar n_14) (array (term_mvar n_17) (array (term_mvar m_18) (type_mvar t_19))))=(array (+ 1 (term_mvar n_21)) (array 4 (array (+ 1 (term_mvar n_27)) (array 4 (type_mvar d_33)))));(array (term_mvar n_31) (array (term_mvar m_32) (type_mvar d_33)))=(type_mvar anonymous_13);(array (+ (* 2 (term_mvar n_21)) 4) (type_mvar t_22))=(array (+ (+ 1 (term_mvar n_31)) (+ 2 (* 2 (- (+ 1 (/ (term_bvar h_1) 2)) (/ (term_bvar h_1) 2))))) (array (+ 1 (term_mvar n_27)) (array 4 (type_mvar d_33))));(array (term_mvar n_31) (array (term_mvar m_32) (type_mvar d_33)))=(type_mvar anonymous_20);(array (term_mvar n_24) (array (+ (* 2 (term_mvar n_27)) 4) (type_mvar t_28)))=(array (+ (+ 1 (term_mvar n_31)) (+ 2 (* 2 (- (+ 1 (/ (term_bvar h_1) 2)) (/ (term_bvar h_1) 2))))) (array (+ (+ 1 (term_mvar m_32)) (+ 2 (* 2 (- (+ 1 (/ (term_bvar w_0) 2)) (/ (term_bvar w_0) 2))))) (type_mvar d_33)));(array (term_mvar n_31) (array (term_mvar m_32) (type_mvar d_33)))=(type_mvar anonymous_23);(-> (type_mvar s_25) (type_mvar t_26))=(-> (array (+ (* 2 (term_mvar n_27)) 4) (type_mvar t_28)) (array (+ 1 (term_mvar n_27)) (array 4 (type_mvar t_28))));(-> (type_mvar s_15) (type_mvar t_16))=(-> (array (term_mvar n_17) (array (term_mvar m_18) (type_mvar t_19))) (array (term_mvar m_18) (array (term_mvar n_17) (type_mvar t_19))));(-> (type_mvar s_2) (type_mvar t_3))=(-> (array (term_mvar n_4) (array 4 (array 4 f32))) (array (term_mvar n_4) f32));(-> (type_mvar s_5) (type_mvar t_6))=(-> (array 4 (array 4 f32)) f32);(array 4 f32)=(array (term_mvar n_9) f32);(array (term_mvar n_9) (array 4 f32))=(type_mvar anonymous_7);(-> (type_mvar s_10) (type_mvar t_11))=(-> (array 4 f32) f32);(array (term_mvar n_12) f32)=(array 4 f32);(array (term_mvar n_8) f32)=(array 4 f32)";
    let r = unify(goals).unwrap();
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
    let goals ="(array (term_mvar n_0) (array (term_mvar m_1) (type_mvar t_2)))=(array (term_mvar n_3) (type_mvar t_5));(array (term_mvar n_3) (type_mvar s_4))=(array (term_mvar m_30) (array (* (* 4 128) 128) (type_mvar t_31)));(array (* (term_mvar m_30) (* (* 4 128) 128)) (type_mvar t_31))=(array (term_bvar n_0) f32);(-> (type_mvar s_4) (type_mvar t_5))=(-> (type_mvar anonymous_6) (array (* (term_mvar m_8) (term_mvar n_7)) (type_mvar t_9)));(array (term_mvar m_8) (vector (term_mvar n_7) (type_mvar t_9)))=(array (* (term_mvar n_11) (term_mvar m_12)) (type_mvar t_13));(type_mvar anonymous_10)=(type_mvar anonymous_6);(array (term_mvar n_11) (array (term_mvar m_12) (type_mvar t_13)))=(array (term_mvar n_15) (type_mvar t_17));(type_mvar anonymous_14)=(type_mvar anonymous_10);(array (term_mvar n_15) (type_mvar s_16))=(array (term_mvar m_26) (array 128 (type_mvar t_27)));(type_mvar anonymous_25)=(type_mvar anonymous_14);(array (* (term_mvar m_26) 128) (type_mvar t_27))=(array (term_mvar m_28) (vector 4 (type_mvar t_29)));(array (* (term_mvar m_28) 4) (type_mvar t_29))=(type_mvar anonymous_25);(-> (type_mvar s_16) (type_mvar t_17))=(-> (array (term_mvar n_18) (type_mvar s_19)) (array (term_mvar n_18) (type_mvar t_20)));(-> (type_mvar s_19) (type_mvar t_20))=(-> (type_mvar anonymous_21) (type_mvar t_22));(type_mvar t_22)=(vector (term_mvar n_23) (type_mvar t_24));(type_mvar t_24)=f32;(type_mvar t_22)=(type_mvar anonymous_21)";
    let r = unify(goals).unwrap();
    assert_eq!(r, map![]);
}
// fn main() {
//     // simple_tests();
//     let _r = unify2(
//         "(-> (type_mvar a) (type_mvar b))",
//         "(-> (type_mvar c) (type_mvar c))",
//     );
//     // dbg!(r);
// }
