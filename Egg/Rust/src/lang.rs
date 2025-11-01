use egg::*;
use std::collections::HashMap;
use std::time::Duration;

define_language! {
    pub enum RiseType {
        "array" = Array([Id; 2]),
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

        multi_rewrite!(s(); "?v = (-> ?a ?b) = (-> ?c ?d)" => "?a = ?c, ?b = ?d"),
        multi_rewrite!(s(); "?v = (array ?a ?b) = (array ?c ?d)" => "?a = ?c, ?b = ?d"),
        multi_rewrite!(s(); "?v = (pair ?a ?b) = (pair ?c ?d)" => "?a = ?c, ?b = ?d"),

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

#[derive(PartialEq, Eq, PartialOrd, Debug, Clone, Copy)]
struct MCost {
    mvars: usize,
    rest: usize,
}

impl Ord for MCost {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        use std::cmp::Ordering::*;
        match self.mvars.cmp(other.mvars) {
            Less => todo!(),
            Equal => todo!(),
            Greater => todo!(),
        }
    }
}

struct UnifyCostFn;
impl CostFunction<RiseType> for UnifyCostFn {
    type Cost = MCost;
    fn cost<C>(&mut self, enode: &RiseType, mut costs: C) -> Self::Cost
    where
        C: FnMut(Id) -> Self::Cost,
    {
        match enode {
            RiseType::Array(_)
            | RiseType::Pair(_)
            | RiseType::Index(_)
            | RiseType::Fn(_)
            | RiseType::Num(_)
            | RiseType::Add(_)
            | RiseType::Mul(_)
            | RiseType::Div(_)
            | RiseType::Sub(_)
            | RiseType::TypeBVar(_)
            | RiseType::TermBVar(_)
            | RiseType::Symbol(_) => enode.fold(MCost { mvars: 0, rest: 1 }, |sum, id| {
                let MCost { mvars, rest } = costs(id);
                MCost {
                    mvars: sum.mvars.saturating_add(mvars),
                    rest: sum.rest.saturating_add(rest),
                }
            }),
            RiseType::TermMVar(_) | RiseType::TypeMVar(_) => {
                MCost { mvars: 1, rest: 0 }
                // enode.fold(MCost { mvars: 1, rest: 0 }, |sum, id| {
                //     let MCost { mvars, rest } = costs(id);
                //     MCost {
                //         mvars: sum.mvars.saturating_add(mvars),
                //         rest: sum.rest.saturating_add(rest),
                //     }
                // })
            }
        }
        // enode.fold(1, |sum, id| sum.saturating_add(costs(id)))
    }
}

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

pub fn unify(s1: &str, s2: &str) -> Result<HashMap<String, String>, String> {
    // setup
    let a: RecExpr<RiseType> = s1.parse().unwrap();
    let b: RecExpr<RiseType> = s2.parse().unwrap();
    let mut eg: EGraph<RiseType, UnifyAnalysis> = EGraph::new(UnifyAnalysis::default());
    let id_a = eg.add_expr(&a);
    let id_b = eg.add_expr(&b);
    eg.union(id_a, id_b);

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
    let extractor = Extractor::new(&runner.egraph, UnifyCostFn {});
    // let extractor = Extractor::new(&runner.egraph, AstSize);
    // dbg!(runner.egraph.dump());
    for class in runner.egraph.classes() {
        if class.nodes.len() == 1 {
            continue;
        };
        if class.nodes.iter().any(|x| is_mvar(x)) {
            let (_cost, x) = extractor.find_best(class.id);
            class.nodes.iter().for_each(|n| {
                if is_mvar(n) {
                    dbg!(_cost, &x);
                    if let Some(p) = pretty_mvar(&runner.egraph, n) {
                        // dbg!(_cost, &x, &p);
                        let x = x.pretty(1000);
                        if x != p {
                            map.insert(p, x);
                        }
                    }
                }
            });
        }
    }
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
    let r = unify(
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
//     let r = unify("(array (+ (type_mvar n1) 2) int)", "(array (+ 2 (type_mvar n2)) int)").unwrap();
//     assert_eq!(r, map![]);
// }

// #[test]
// fn t_vhspy() {
//     let r = unify("(array (+ (type_mvar n1) 2) int)", "(array (+ 3 (type_mvar n2)) int)").unwrap();
//     assert_eq!(r, map![]);
// }

// #[test]
// fn t_c1mju() {
//     let r = unify("(array (type_mvar n1) int)", "(array (type_mvar n2) int)").unwrap();
//     assert_eq!(r, map![]);
// }

#[test]
fn t_9k0px() {
    let r = unify("(-> int (type_mvar b))", "(-> f32 (type_mvar c))");
    assert!(r.is_err());
}

#[test]
fn t_lq6oe() {
    let r = unify("(-> int (type_mvar b))", "(-> bool (type_mvar c))");
    assert!(r.is_err());
}

#[test]
fn t_lr6oe() {
    let r = unify(
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
    let r = unify("(-> int (type_mvar b))", "(-> int (type_mvar c))").unwrap();
    assert_eq!(r, map![("(type_mvar c)", "(type_mvar b)")]);
}

#[test]
fn t_bhru() {
    let r = unify(
        "(-> (type_mvar a) (type_mvar b))",
        "(-> (type_mvar b) (type_mvar a))",
    )
    .unwrap();
    assert_eq!(r, map![("(type_mvar b)", "(type_mvar a)")]);
}

#[test]
fn t_kxpva() {
    let r = unify(
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
    let r = unify("(pair (type_mvar a) (type_mvar b))", "(type_mvar c)").unwrap();
    assert_eq!(
        r,
        map![("(type_mvar c)", "(pair (type_mvar a) (type_mvar b))")]
    );
}

#[test]
fn t_didhl() {
    let r = unify(
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
    let r = unify(
        "(-> (type_mvar a) (type_mvar b))",
        "(-> (type_mvar a) (type_mvar c))",
    )
    .unwrap();
    assert_eq!(r, map![("(type_mvar c)", "(type_mvar b)")]);
}
#[test]
fn t_qr5of() {
    let r = unify("(term_mvar a)", "(+ 1 0)").unwrap();
    assert_eq!(r, map![("(term_mvar a)", "1")]);
}
#[test]
fn t_qllof() {
    let r = unify("(term_mvar a)", "(+ 1 (term_mvar a))").unwrap();
    assert_eq!(r, map![("(term_mvar a)", "1")]);
}

// fn main() {
//     // simple_tests();
//     let _r = unify(
//         "(-> (type_mvar a) (type_mvar b))",
//         "(-> (type_mvar c) (type_mvar c))",
//     );
//     // dbg!(r);
// }
