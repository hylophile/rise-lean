use egg::*;
use std::collections::HashMap;
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

fn dt_rules() -> Vec<Rewrite<RiseType, UnifyAnalysis>> {
    vec![
        // datatypes
        multi_rewrite!(s(); "?v = (-> ?a ?b) = (-> ?c ?d)" => "?a = ?c, ?b = ?d"),
        multi_rewrite!(s(); "?v = (array ?a ?b) = (array ?c ?d)" => "?a = ?c, ?b = ?d"),
        multi_rewrite!(s(); "?v = (vector ?a ?b) = (vector ?c ?d)" => "?a = ?c, ?b = ?d"),
        multi_rewrite!(s(); "?v = (pair ?a ?b) = (pair ?c ?d)" => "?a = ?c, ?b = ?d"),
        multi_rewrite!(s(); "?v = (index ?a) = (index ?c)" => "?a = ?c"),
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
        Some((n, _)) => n != 0,
        None => true,
    }
}
fn is_not_const(var: &'static str) -> impl Fn(&mut EGraph, Id, &Subst) -> bool {
    let var = var.parse().unwrap();
    move |egraph, _, subst| match egraph[subst[var]].data.const_prop {
        Some(_) => false,
        None => true,
    }
}
fn imm_is_not_zero(var: &'static str) -> impl Fn(&EGraph, Id, &Subst) -> bool {
    let var = var.parse().unwrap();
    // let zero = RiseType::Num(0);
    // note this check is just an example,
    // checking for the absence of 0 is insufficient since 0 could be merged in later
    // see https://github.com/egraphs-good/egg/issues/297
    // move |egraph, _, subst| !egraph[subst[var]].nodes.contains(&zero)
    move |egraph, _, subst| match egraph[subst[var]].data.const_prop {
        Some((n, _)) => n != 0,
        None => true,
    }
}
fn imm_is_not_const(var: &'static str) -> impl Fn(&EGraph, Id, &Subst) -> bool {
    let var = var.parse().unwrap();
    move |egraph, _, subst| match egraph[subst[var]].data.const_prop {
        Some(_) => false,
        None => true,
    }
}
// fn imm_is_mvar(var: &'static str) -> impl Fn(&EGraph, Id, &Subst) -> bool {
//     let var = var.parse().unwrap();
//     // move |egraph, _, subst| match egraph[subst[var]].data.variant {
//     //     Variant::TermMVar => true,
//     //     _ => false,
//     // }
//     move |egraph, _, subst| egraph[subst[var]].nodes.iter().any(|n| is_mvar(n))
// }

// multi_rewrite!(s(); "?c = (+ ?a ?b)" => "?b = (- ?c ?a)"),
struct AddInverse;
impl Applier<RiseType, UnifyAnalysis> for AddInverse {
    fn apply_one(
        &self,
        egraph: &mut EGraph,
        _eclass: Id,
        subst: &Subst,
        _searcher_ast: Option<&PatternAst<RiseType>>,
        _rule_name: Symbol,
    ) -> Vec<Id> {
        let f = |s| imm_is_not_const(s)(egraph, _eclass, subst);
        let g = |s| imm_is_not_zero(s)(egraph, _eclass, subst);
        // let h = |s| imm_is_mvar(s)(egraph, _eclass, subst);
        let a_id = subst["?a".parse().unwrap()];
        let b_id = subst["?b".parse().unwrap()];
        let c_id = subst["?c".parse().unwrap()];
        // if f("?b") && f("?c") {
        if f("?b") && g("?c") {
            let x = egraph.add(RiseType::Sub([c_id, a_id]));
            let _ = egraph.union(b_id, x);
            vec![x, b_id]
        } else {
            vec![]
        }
    }
}

// "?c = (* ?a ?b)" => "?b = (/ ?c ?a)" if a != 0
struct DivInverse;
impl Applier<RiseType, UnifyAnalysis> for DivInverse {
    fn apply_one(
        &self,
        egraph: &mut EGraph,
        _eclass: Id,
        subst: &Subst,
        _searcher_ast: Option<&PatternAst<RiseType>>,
        _rule_name: Symbol,
    ) -> Vec<Id> {
        let f = |s| imm_is_not_const(s)(egraph, _eclass, subst);
        let g = |s| imm_is_not_zero(s)(egraph, _eclass, subst);
        let a_id = subst["?a".parse().unwrap()];
        let b_id = subst["?b".parse().unwrap()];
        let c_id = subst["?c".parse().unwrap()];
        // if f("?a") && f("?b") && f("?c") {
        // if g("?a") && g("?b") && g("?c") && f("?c") && f("?b") && !g("?a") {
        // if g("?a") && f("?b") && f("?c") {
        if g("?a") {
            // if g("?a") && g("?b") && g("?c") {
            let x = egraph.add(RiseType::Div([c_id, a_id]));
            let _ = egraph.union(b_id, x);
            vec![x, b_id]
        } else {
            vec![]
        }
    }
}

#[rustfmt::skip]
fn nat_rules() -> Vec<Rewrite<RiseType, UnifyAnalysis>> {
    // let x =  {
    //     let searcher = egg::__rewrite!(@parse MultiPattern "?c = (* ?a ?b)");
    //     let core_applier = egg::__rewrite!(@parse MultiPattern "?b = (/ ?c ?a)");
    //     let applier = egg::__rewrite!(@applier core_applier; is_not_zero("?a"),);
    //     egg::Rewrite::new((s()).to_string(),searcher,applier).unwrap()
    // };
    vec![
        // add
        rewrite!("add-comm"; "(+ ?a ?b)" => "(+ ?b ?a)"),
        rewrite!("add-assoc"; "(+ ?a (+ ?b ?c))" => "(+ (+ ?a ?b) ?c)"),
        rewrite!("add-assoc2"; "(+ (+ ?a ?b) ?c)" => "(+ ?a (+ ?b ?c))"),
        rewrite!("add-zero"; "(+ ?a 0)" => "?a"),

        // add-sub
        rewrite!("add-sub-assoc"; "(+ ?a (- ?b ?c))" => "(- (+ ?a ?b) ?c)"),
        // adding the second one makes graph inconsistent?
        rewrite!("add-sub-assoc2"; "(- (+ ?a ?b) ?c)" => "(+ ?a (- ?b ?c))"),
        
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
        multi_rewrite!(s(); "?c = (/ ?a ?b)" => "?a = (* ?c ?b)"),

        // div-add
        rewrite!(s(); "(/ (+ ?a ?b) ?c)" => "(+ (/ ?a ?c) (/ ?b ?c))" if is_not_zero("?b") if is_not_zero("?c")),

        // more. expensive
        multi_rewrite!(s(); "?c = (* ?a ?b)" => DivInverse ),
        multi_rewrite!(s(); "?c = (+ ?a ?b)" => AddInverse),

        // multi_rewrite!(s(); "?p = (term_mvar ?c) = (+ (term_mvar ?a) ?b)" => "?q = (term_mvar ?a) = (- (term_mvar ?c) (term_mvar ?b))"),
        // multi_rewrite!(s(); "?p = (term_bvar ?c) = (+ (term_mvar ?a) ?b)" => "?q = (term_mvar ?a) = (- (term_bvar ?c) (term_mvar ?b))"),
        ]
}

#[rustfmt::skip]
fn nat_rules_expensive() -> Vec<Rewrite<RiseType, UnifyAnalysis>> {
    vec![
        multi_rewrite!(s(); "?c = (* ?a ?b)" => DivInverse ),
        multi_rewrite!(s(); "?c = (+ ?a ?b)" => AddInverse),
    ]
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
    const_prop: Option<(i32, PatternAst<RiseType>)>,
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

fn clean_divide(x: i32, y: i32) -> Option<i32> {
    if x % y == 0 {
        Some(x / y)
    } else {
        None
    }
}

fn make_const_prop(egraph: &mut EGraph, enode: &RiseType) -> Option<(i32, PatternAst<RiseType>)> {
    let x = |i: &Id| egraph[*i].data.const_prop.as_ref().map(|d| d.0);
    Some(match enode {
        RiseType::Num(c) => (*c, format!("{}", c).parse().unwrap()),
        RiseType::Add([a, b]) => (
            x(a)? + x(b)?,
            format!("(+ {} {})", x(a)?, x(b)?).parse().unwrap(),
        ),
        RiseType::Sub([a, b]) => (
            // {
            //     let r = x(a)? - x(b)?;
            //     if r > 0 {
            //         r
            //     } else {
            //         return None;
            //     }
            // },
            x(a)? - x(b)?,
            format!("(- {} {})", x(a)?, x(b)?).parse().unwrap(),
        ),
        RiseType::Mul([a, b]) => (
            // x(a)? * x(b)?,
            x(a)?.checked_mul(x(b)?)?,
            format!("(* {} {})", x(a)?, x(b)?).parse().unwrap(),
        ),
        RiseType::Div([a, b]) if x(b) != Some(0) => (
            clean_divide(x(a)?, x(b)?)?,
            format!("(/ {} {})", x(a)?, x(b)?).parse().unwrap(),
        ),
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
                if x.0 != y.0 {
                    self.found_err = Err(format!("merged unequal constants {} and {}", x.0, y.0))
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
        let data = egraph[id].data.const_prop.clone();
        if let Some((c, _pat)) = data {
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

pub fn unify(input: &str) -> Result<HashMap<String, String>, String> {
    let goals: Vec<(&str, &str)> = input
        .split(';')
        .filter(|x| *x != "")
        .map(|x| x.split_once('=').ok_or(format!("invalid input: {input}")))
        .collect::<Result<Vec<(&str, &str)>, String>>()?;

    // setup
    let mut eg: EGraph = EGraph::new(UnifyAnalysis::default());
    for (s1, s2) in goals {
        let a: RecExpr<RiseType> = s1.parse().unwrap();
        let b: RecExpr<RiseType> = s2.parse().unwrap();
        let id_a = eg.add_expr(&a);
        let id_b = eg.add_expr(&b);
        eg.union(id_a, id_b);
    }

    // run
    let runner: Runner<RiseType, UnifyAnalysis> =
        Runner::default().with_egraph(eg).run(&dt_rules());
    let runner = Runner::default()
        .with_egraph(runner.egraph)
        .with_iter_limit(3)
        .run(&nat_rules());
    // let runner = Runner::default()
    //     .with_egraph(runner.egraph)
    //     .with_iter_limit(3)
    //     .run(&nat_rules_expensive());
    // let runner = Runner::default()
    //     .with_egraph(runner.egraph)
    //     .with_iter_limit(5)
    //     .run(&nat_rules());
    let eg = runner.egraph;

    #[cfg(all(test, feature = "dot"))]
    eg.dot().to_svg("target/foo.svg").unwrap();
    #[cfg(all(test, feature = "dot"))]
    dbg!(eg.dump());

    for class in eg.classes() {
        check_no_self_loops(&eg, class)?
    }

    let _ = &eg.analysis.found_err.clone()?;

    let mut map = HashMap::new();
    for class in eg.classes() {
        // find repr
        //
        let init = get_repr(&eg, class.id);
        let repr: RecExpr<RiseType> = init.build_recexpr(|n| get_repr(&eg, n));
        // let repr: RecExpr<RiseType> = eg[class.id].bui

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
    Ok(map)
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
