use egg::*;
use std::collections::HashMap;
use std::env;
use std::time::Duration;
// use std::time::Duration;

type EGraph = egg::EGraph<RiseType, UnifyAnalysis>;
type EClass = egg::EClass<RiseType, InnerAnalysis>;

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
        "~" = Unify([Id; 2]),
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

fn dt_rules() -> Vec<Rewrite<RiseType, UnifyAnalysis>> {
    vec![
        // datatypes
        rewrite!("t-comm"; "(~ ?a ?b)" => "(~ ?b ?a)"),
        multi_rewrite!(s(); "?v = (~ (-> ?a ?b) (-> ?c ?d))" => "?w = (~ ?a ?c), ?x = (~ ?b ?d)"),
        multi_rewrite!(s(); "?v = (~ (vector ?a ?b) (vector ?c ?d))" => "?w = (~ ?a ?c), ?x = (~ ?b ?d)"),
        multi_rewrite!(s(); "?v = (~ (pair ?a ?b) (pair ?c ?d))" => "?w = (~ ?a ?c), ?x = (~ ?b ?d)"),
        multi_rewrite!(s(); "?v = (~ (array ?a ?b) (array ?c ?d))" => "?w = (~ ?a ?c), ?x = (~ ?b ?d)"),
        multi_rewrite!(s(); "?v = (~ (index ?a) (index ?c))" => "?w = (~ ?a ?c)"),
        multi_rewrite!(s(); "?a = (type_mvar ?v), ?p = (~ ?a ?b)" => "?a = ?b"), // if no analysis conflict...
    ]
}

#[rustfmt::skip]
fn nat_rules_shift() -> Vec<Rewrite<RiseType, UnifyAnalysis>> {
    vec![
        rewrite!("add-comm"; "(+ ?a ?b)" => "(+ ?b ?a)"),
        rewrite!("mul-comm"; "(* ?a ?b)" => "(* ?b ?a)"),
        rewrite!("t-comm"; "(~ ?a ?b)" => "(~ ?b ?a)"),
        rewrite!(s(); "(~ ?c (/ ?a ?b))" => "(~ (* ?c ?b) ?a)" if is_not_zero("?b")),
        rewrite!(s(); "(~ ?c (* ?a ?b))" => "(~ (/ ?c ?b) ?a)" if is_not_zero("?b")),
        rewrite!(s(); "(~ ?c (+ ?a ?b))" => "(~ (- ?c ?b) ?a)"),
        rewrite!(s(); "(~ ?c (- ?a ?b))" => "(~ (+ ?c ?b) ?a)"),
        multi_rewrite!(s(); "?p=(term_mvar ?a), ?q = (~ (term_mvar ?a) ?b)" => "?p = ?b"),
        // rewrite!("t-comm2"; "(~ ?a ?b)" => "(~ ?b ?a)"),
        // multi_rewrite!(s(); "?p = (~ ?a ?b), ?q = (~ ?a ?c)" => "?r = (~ ?b ?c)"),
        // multi_rewrite!(s(); "?q = (~ (term_mvar ?a) ?b), ?p = (~ (term_mvar ?a) ?c)" => "?b = ?c"),
        // multi_rewrite!(s(); "?q = (~ (term_mvar ?a) (term_mvar ?b))" => "?p = (term_mvar ?a) = (term_mvar ?b)"),
    ]
}

#[rustfmt::skip]
fn nat_rules() -> Vec<Rewrite<RiseType, UnifyAnalysis>> {
    vec![
        // add
        rewrite!("add-comm"; "(+ ?a ?b)" => "(+ ?b ?a)"),
        rewrite!("add-assoc"; "(+ ?a (+ ?b ?c))" => "(+ (+ ?a ?b) ?c)"),
        rewrite!("add-zero"; "(+ ?a 0)" => "?a"),

        // add-sub
        rewrite!("add-sub-assoc"; "(+ ?a (- ?b ?c))" => "(- (+ ?a ?b) ?c)"),
        rewrite!("add-sub-assoc2"; "(- (+ ?a ?b) ?c)" => "(+ ?a (- ?b ?c))"),
        rewrite!("add-sub-assoc3"; "(- ?c (+ ?a ?b))" => "(- (- ?c ?a) ?b)"),
        

        rewrite!("sub-canon"; "(- ?a ?b)" => "(+ ?a (* -1 ?b))"),
        rewrite!("sub-canon2"; "(+ ?b (* -1 ?b))" => "0"),
        // rewrite!("div-canon"; "(/ ?a ?b)" => "(* ?a (pow ?b -1))" if is_not_zero("?b")),
        
        // sub
        rewrite!("sub-zero"; "(- ?a 0)" => "?a"),
        rewrite!("sub-self"; "(- ?a ?a)" => "0"),

        // mul
        rewrite!("mul-comm"; "(* ?a ?b)" => "(* ?b ?a)"),
        rewrite!("mul-assoc"; "(* ?a (* ?b ?c))" => "(* (* ?a ?b) ?c)"),
        rewrite!("mul-one"; "(* ?a 1)" => "?a"),
        rewrite!("mul-zero"; "(* 0 ?a)" => "0"),
        rewrite!("mul-distrib"; "(* ?a (+ ?b ?c))" => "(+ (* ?a ?b) (* ?a ?c))"),

        // div
        rewrite!("div-one"; "(/ ?a 1)" => "?a"),
        rewrite!("div-self"; "(/ ?a ?a)" => "1" if is_not_zero("?a")),

        // div-mul
        rewrite!(s(); "(* ?a (/ ?b ?a))" => "?b" if is_not_zero("?a")),
        rewrite!(s(); "(/ ?a (/ ?b ?c))" => "(* ?a (/ ?c ?b))" if is_not_zero("?b")),
        rewrite!(s(); "(/ (/ ?a ?b) ?c)" => "(/ ?a (* ?b ?c))" if is_not_zero("?b") if is_not_zero("?c")),

        // div-add
        rewrite!(s(); "(/ (+ ?a ?b) ?c)" => "(+ (/ ?a ?c) (/ ?b ?c))" if is_not_zero("?b") if is_not_zero("?c")),
        rewrite!(s(); "(+ ?a (/ ?b ?c))" => "(/ (+ (* ?a ?c) ?b) ?c)"),

        // multi_rewrite!(s(); "?q = (~ (term_mvar ?a) (term_mvar ?b))" => "?p = (term_mvar ?a) = (term_mvar ?b)"),

        // multi_rewrite!(s(); "?q = (~ (term_mvar ?a) ?b), ?p = (~ (term_mvar ?a) ?c)" => "?b = ?c"),
        // multi_rewrite!(s(); "?q = (term_mvar ?a), ?p = (~ ?q ?b)" => "?q = ?b"),
        

        ]
}

fn is_not_zero(var: &'static str) -> impl Fn(&mut EGraph, Id, &Subst) -> bool {
    let var = var.parse().unwrap();
    // let zero = RiseType::Num(0);
    // note this check is just an example,
    // checking for the absence of 0 is insufficient since 0 could be merged in later
    // see https://github.com/egraphs-good/egg/issues/297
    // move |egraph, _, subst| !egraph[subst[var]].nodes.contains(&zero)
    move |egraph, _, subst| match egraph[subst[var]].data.const_prop {
        Some(n) => n != 0,
        None => true,
    }
}

#[derive(Debug, Clone)]
struct UnifyAnalysis {
    found_err: Result<(), String>,
}

impl Default for UnifyAnalysis {
    fn default() -> Self {
        Self { found_err: Ok(()) }
    }
}

fn check_no_self_loops(egraph: &EGraph, class: &EClass) -> Result<(), String> {
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
struct InnerAnalysis {
    variant: Variant,
    const_prop: Option<i32>,
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
        | RiseType::Unify(_)
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

fn clean_divide(x: i32, y: i32) -> Option<i32> {
    if x % y == 0 {
        Some(x / y)
    } else {
        None
    }
}

fn make_const_prop(egraph: &mut EGraph, enode: &RiseType) -> Option<i32> {
    let x = |i: &Id| egraph[*i].data.const_prop;
    Some(match enode {
        RiseType::Num(c) => *c,
        RiseType::Add([a, b]) => x(a)? + x(b)?,
        RiseType::Sub([a, b]) => x(a)? - x(b)?,
        RiseType::Mul([a, b]) => x(a)?.checked_mul(x(b)?)?,
        RiseType::Div([a, b]) if x(b) != Some(0) => clean_divide(x(a)?, x(b)?)?,
        _ => return None,
    })
}

impl Analysis<RiseType> for UnifyAnalysis {
    type Data = InnerAnalysis;

    fn make(egraph: &mut EGraph, enode: &RiseType) -> Self::Data {
        InnerAnalysis {
            variant: get_variant(enode),
            const_prop: make_const_prop(egraph, enode),
        }
    }

    fn merge(&mut self, a: &mut Self::Data, b: Self::Data) -> DidMerge {
        use Variant::*;
        let (new_val, a_changed, b_changed) = match (a.variant.clone(), b.variant.clone()) {
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
                    self.found_err = Err(format!("merge conflict: {a:?} {b:?}"));
                    (TypeName(s1.clone()), false, false)
                }
            }

            (_, v) => {
                self.found_err = Err(format!("merge conflict: {a:?} {b:?}"));
                (v, false, false)
            }
        };

        let (new_c, a_c, b_c) = match (a.const_prop.clone(), b.const_prop) {
            (None, None) => (None, false, false),
            (None, Some(x)) => (Some(x), true, false),
            (Some(x), None) => (Some(x), false, true),
            (Some(x), Some(y)) => {
                if x != y {
                    self.found_err = Err(format!("merged unequal constants {} and {}", x, y))
                }
                (Some(x), false, false)
            }
        };

        *a = InnerAnalysis {
            variant: new_val,
            const_prop: new_c,
        };
        DidMerge(a_changed || a_c, b_changed || b_c)
    }

    fn modify(egraph: &mut EGraph, id: Id) {
        match egraph.analysis.found_err.clone() {
            Ok(_) => (),
            Err(s) => {
                if s.contains("unequal") {
                    egraph.analysis.found_err = Err(format!("id {id}; {s}"))
                }
            }
        }
        let data = egraph[id].data.const_prop.clone();
        if let Some(c) = data {
            // if egraph.are_explanations_enabled() {
            //     egraph.union_instantiations(
            //         &pat,
            //         &format!("{}", c).parse().unwrap(),
            //         &Default::default(),
            //         "constant_fold".to_string(),
            //     );
            // } else {
            let added = egraph.add(RiseType::Num(c));
            egraph.union(id, added);
            // }
            // to not prune, comment this out
            // egraph[id]
            //     .nodes
            //     .retain(|n| n.is_leaf() || is_mvar(n) || is_bvar(n));

            // #[cfg(debug_assertions)]
            // egraph[id].assert_unique_leaves();
        }
    }
}

fn is_mvar(l: &RiseType) -> bool {
    match l {
        RiseType::TermMVar(_) | RiseType::TypeMVar(_) => true,
        _ => false,
    }
}
fn is_bvar(l: &RiseType) -> bool {
    match l {
        RiseType::TermBVar(_) | RiseType::TypeBVar(_) => true,
        _ => false,
    }
}

fn pretty_mvar(egraph: &EGraph, l: &RiseType) -> Option<String> {
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

struct SillyCostFn;
impl CostFunction<RiseType> for SillyCostFn {
    type Cost = i32;
    fn cost<C>(&mut self, enode: &RiseType, mut costs: C) -> Self::Cost
    where
        C: FnMut(Id) -> Self::Cost,
    {
        let op_cost = match enode {
            RiseType::TermMVar(_) => 100,
            // RiseType::Num(_) => todo!(),
            // RiseType::Add(_) => todo!(),
            // RiseType::Mul(_) => todo!(),
            // RiseType::Div(_) => todo!(),
            // RiseType::Sub(_) => todo!(),
            // RiseType::TermBVar(id) => todo!(),
            _ => 1,
        };
        enode.fold(op_cost, |sum, id| sum + costs(id))
    }
}

struct ExcludingIdCostFn {
    top: bool,
    id: Id,
}

impl CostFunction<RiseType> for ExcludingIdCostFn {
    type Cost = i32;
    fn cost<C>(&mut self, enode: &RiseType, mut costs: C) -> Self::Cost
    where
        C: FnMut(Id) -> Self::Cost,
    {
        let op_cost = match enode {
            RiseType::TermMVar(id) => {
                if &self.id == id {
                    i32::MAX
                } else {
                    100
                }
            }
            // RiseType::Num(_) => todo!(),
            // RiseType::Add(_) => todo!(),
            // RiseType::Mul(_) => todo!(),
            // RiseType::Div(_) => todo!(),
            // RiseType::Sub(_) => todo!(),
            // RiseType::TermBVar(id) => todo!(),
            _ => 1,
        };
        // self.top = false;
        enode.fold(op_cost, |sum, id| sum.saturating_add(costs(id)))
    }
}

pub fn unify(input: &str) -> Result<HashMap<String, String>, String> {
    // let goals: Vec<&str> = input.split(';').filter(|x| *x != "").collect::<Vec<&str>>();
    let goals: Vec<(&str, &str)> = input
        .split(';')
        .filter(|x| *x != "")
        .map(|x| x.split_once('=').ok_or(format!("invalid input: {input}")))
        .collect::<Result<Vec<(&str, &str)>, String>>()?;

    // setup
    let mut eg: EGraph = EGraph::new(UnifyAnalysis::default()); //.with_explanations_enabled();
    for (s1, s2) in goals {
        let a: RecExpr<RiseType> = (format!("(~ {s1} {s2})")).parse().unwrap();
        let _id_a = eg.add_expr(&a);
    }

    // run
    let mut runner: Runner<RiseType, UnifyAnalysis> =
        Runner::default().with_egraph(eg).run(&dt_rules());
    let mut counter = 0;
    // while counter < 4 && runner.egraph.analysis.found_err.is_ok() {
    runner = Runner::default()
        .with_egraph(runner.egraph)
        .with_scheduler(BackoffScheduler::default().do_not_ban("assoc-plus"))
        // .with_scheduler(SimpleScheduler {})
        // .with_iter_limit(5)
        .run(&nat_rules_shift());
    //     counter += 1;
    // }

    let eg = runner.egraph;

    #[cfg(feature = "dot")]
    eg.dot().to_svg("target/foo.svg").unwrap();
    // #[cfg(feature = "dot")]
    // dbg!(eg.dump());

    let _ = &eg.analysis.found_err.clone()?;

    for class in eg.classes() {
        check_no_self_loops(&eg, class)?
    }

    let s3: Pattern<RiseType> = "(~ (term_mvar ?a) ?b)".parse().unwrap();
    let mut neweg = EGraph::new(UnifyAnalysis::default());
    let p = s3.search(&eg);
    for m in p {
        for s in m.substs {
            let pid_a = s["?a".parse().unwrap()];
            let a = get_repr(&eg, pid_a);
            let r = RecExpr::from(vec![a.clone(), RiseType::TermMVar(0.into())]);
            let id_a = neweg.add_expr(&r);

            let b = &pq(&eg, s["?b".parse().unwrap()]);
            let id_b = neweg.add_expr(b);
            neweg.union(id_a, id_b);
            // neweg.add(RiseType::Unify([id_a, id_b]));
            // eprintln!(
            //     "{}: {}",
            //     RecExpr::from(vec![a]).pretty(1000),
            //     b.pretty(1000)
            // );
        }
    }
    // let s3: Pattern<RiseType> = "(~ (type_mvar ?a) ?b)".parse().unwrap();
    // // let mut neweg = EGraph::new(UnifyAnalysis::default());
    // let p = s3.search(&eg);
    // for m in p {
    //     for s in m.substs {
    //         let pid_a = s["?a".parse().unwrap()];
    //         let a = get_repr(&eg, pid_a);
    //         let r = RecExpr::from(vec![a.clone(), RiseType::TypeMVar(0.into())]);
    //         let id_a = neweg.add_expr(&r);

    //         let b = &pq(&eg, s["?b".parse().unwrap()]);
    //         let id_b = neweg.add_expr(b);
    //         neweg.union(id_a, id_b);
    //         // neweg.add(RiseType::Unify([id_a, id_b]));
    //         // eprintln!(
    //         //     "{}: {}",
    //         //     RecExpr::from(vec![a]).pretty(1000),
    //         //     b.pretty(1000)
    //         // );
    //     }
    // }
    // let neweg = eg;

    let iters = std::env::var("ITERS")
        .expect("no iters set")
        .parse::<usize>()
        .expect("cant parse usize in iters");
    let mut runner: Runner<RiseType, UnifyAnalysis> = Runner::default()
        .with_egraph(neweg)
        // .with_scheduler(SimpleScheduler {})
        .with_iter_limit(iters)
        // .with_time_limit(Duration::from_secs(5))
        .run(&nat_rules());

    // while counter < 4 && runner.egraph.analysis.found_err.is_ok() {
    //     runner = Runner::default()
    //         .with_egraph(runner.egraph)
    //         .with_iter_limit(20)
    //         .run(&nat_rules());
    //     counter += 1;
    // }
    let eg = runner.egraph;
    // #[cfg(feature = "dot")]
    // eg.dot().to_svg("target/foo.svg").unwrap();

    // dbg!(eg.dump());
    let mut map = HashMap::new();
    for class in eg.classes() {
        // find repr
        let init = get_repr(&eg, class.id);
        let repr: RecExpr<RiseType> = init.build_recexpr(|n| get_repr(&eg, n));

        for mvar in class.nodes.iter().filter(|n| is_mvar(n)) {
            // assign repr
            if let Some(p) = pretty_mvar(&eg, mvar) {
                let repr = repr.pretty(1000);
                if repr != p {
                    map.insert(p, repr);
                }
            }
        }
    }

    // let s3: Pattern<RiseType> = "(~ (term_mvar n_1) ?b)".parse().unwrap();
    // let mut neweg = EGraph::new(UnifyAnalysis::default());
    // let p = s3.search(&eg);
    // for m in p {
    //     for s in m.substs {
    //         // let pid_a = s["?a".parse().unwrap()];
    //         let pid_a = 0.into();
    //         let a = get_repr(&eg, pid_a);
    //         let r = RecExpr::from(vec![a.clone(), RiseType::TermMVar(0.into())]);
    //         let id_a = neweg.add_expr(&r);

    //         let b = &pq_excl(&eg, s["?b".parse().unwrap()], pid_a);
    //         let id_b = neweg.add_expr(b);
    //         neweg.union(id_a, id_b);
    //         // neweg.add(RiseType::Unify([id_a, id_b]));
    //         eprintln!(
    //             "{}: {}",
    //             RecExpr::from(vec![a]).pretty(1000),
    //             b.pretty(1000)
    //         );
    //     }
    // }
    Ok(map)
}

fn pq(eg: &EGraph, id: Id) -> RecExpr<RiseType> {
    let init = get_repr(&eg, id);
    let repr: RecExpr<RiseType> = init.build_recexpr(|n| get_repr(&eg, n));
    repr
}

fn pq_excl(eg: &EGraph, id: Id, ex: Id) -> RecExpr<RiseType> {
    let init = get_repr_excl(&eg, id, ex);
    let repr: RecExpr<RiseType> = init.build_recexpr(|n| get_repr_excl(&eg, n, n));
    repr
}

fn ppp(eg: &EGraph, id: Id) -> String {
    let init = get_repr(&eg, id);
    let repr: RecExpr<RiseType> = init.build_recexpr(|n| get_repr(&eg, n));
    repr.pretty(1000)
}

fn get_repr(eg: &EGraph, id: Id) -> RiseType {
    let class = eg[id].clone();
    match get_variant(&class.nodes[0]) {
        Variant::Term | Variant::TermMVar => {
            let ex = Extractor::new(&eg, SillyCostFn {});
            let v = ex.find_best_node(id);
            v.clone()
        }
        _ => {
            let non_mvars = class
                .nodes
                .iter()
                .filter(|n| !is_mvar(n))
                .collect::<Vec<_>>();
            match non_mvars.len() {
                0 => {
                    // first mvar
                    class.nodes[0].clone()
                }
                1 => non_mvars[0].clone(),
                _ => {
                    panic!("found multiple non_mvars: {non_mvars:?}")
                }
            }
        }
    }
}
fn get_repr_excl(eg: &EGraph, id: Id, ex: Id) -> RiseType {
    // dbg!(id, &eg[id]);
    // dbg!(id);
    let class = eg[id].clone();
    match get_variant(&class.nodes[0]) {
        Variant::Term | Variant::TermMVar => {
            let ex = Extractor::new(&eg, SillyCostFn {});
            // let ex = Extractor::new(&eg, ExcludingIdCostFn { top: true, id: ex });
            let v = ex.find_best_node(id);
            v.clone()
        }
        _ => {
            let non_mvars = class
                .nodes
                .iter()
                .filter(|n| !is_mvar(n))
                .collect::<Vec<_>>();
            match non_mvars.len() {
                0 => {
                    // first mvar
                    class.nodes[0].clone()
                }
                1 => non_mvars[0].clone(),
                _ => {
                    panic!("found multiple non_mvars: {non_mvars:?}")
                }
            }
        }
    }
}
