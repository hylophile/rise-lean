use egg::*;
use std::collections::HashMap;

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
        "data_mvar" = DataMVar(Id),
        "data_bvar" = DataBVar(Id),
        "nat_mvar" = NatMVar(Id),
        "nat_bvar" = NatBVar(Id),
        Symbol(Symbol),
    }
}

use rand::distr::Alphanumeric;
use rand::{rng, Rng};

// generate random rule name
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
        multi_rewrite!(s(); "?a = (data_mvar ?v), ?p = (~ ?a ?b)" => "?a = ?b"), // conflict checked by analysis::merge
    ]
}

#[rustfmt::skip]
fn nat_rules_isolate() -> Vec<Rewrite<RiseType, UnifyAnalysis>> {
    vec![
        rewrite!("add-comm"; "(+ ?a ?b)" => "(+ ?b ?a)"),
        rewrite!("mul-comm"; "(* ?a ?b)" => "(* ?b ?a)"),
        rewrite!("t-comm"; "(~ ?a ?b)" => "(~ ?b ?a)"),
        rewrite!(s(); "(~ ?c (/ ?a ?b))" => "(~ (* ?c ?b) ?a)" if is_not_zero("?b")),
        rewrite!(s(); "(~ ?c (* ?a ?b))" => "(~ (/ ?c ?b) ?a)" if is_not_zero("?b")),
        rewrite!(s(); "(~ ?c (+ ?a ?b))" => "(~ (- ?c ?b) ?a)"),
        rewrite!(s(); "(~ ?c (- ?a ?b))" => "(~ (+ ?c ?b) ?a)"),
        multi_rewrite!(s(); "?p=(nat_mvar ?a), ?q = (~ (nat_mvar ?a) ?b)" => "?p = ?b"),
        // rewrite!("t-comm2"; "(~ ?a ?b)" => "(~ ?b ?a)"),
        // multi_rewrite!(s(); "?p = (~ ?a ?b), ?q = (~ ?a ?c)" => "?r = (~ ?b ?c)"),
        // multi_rewrite!(s(); "?q = (~ (nat_mvar ?a) ?b), ?p = (~ (nat_mvar ?a) ?c)" => "?b = ?c"),
        // multi_rewrite!(s(); "?q = (~ (nat_mvar ?a) (nat_mvar ?b))" => "?p = (nat_mvar ?a) = (nat_mvar ?b)"),
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

        // multi_rewrite!(s(); "?q = (~ (nat_mvar ?a) (nat_mvar ?b))" => "?p = (nat_mvar ?a) = (nat_mvar ?b)"),

        // multi_rewrite!(s(); "?q = (~ (nat_mvar ?a) ?b), ?p = (~ (nat_mvar ?a) ?c)" => "?b = ?c"),
        // multi_rewrite!(s(); "?q = (nat_mvar ?a), ?p = (~ ?q ?b)" => "?q = ?b"),
        

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
        if get_variant(enode) == Variant::Nat {
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
    Nat,
    NatMVar,
    DataMVar,
    DataName(String),
}
fn get_variant(i: &RiseType) -> Variant {
    match i {
        RiseType::NatBVar(_)
        | RiseType::Num(_)
        | RiseType::Add(_)
        | RiseType::Mul(_)
        | RiseType::Div(_)
        | RiseType::Unify(_)
        | RiseType::Sub(_) => Variant::Nat,
        RiseType::DataMVar(_) => Variant::DataMVar,
        RiseType::NatMVar(_) => Variant::NatMVar,
        RiseType::Symbol(s) => Variant::DataName(s.to_string()),
        RiseType::DataBVar(_) => Variant::DataName("bvar".to_string()),
        RiseType::Array(_) => Variant::DataName("array".to_string()),
        RiseType::Vector(_) => Variant::DataName("array".to_string()),
        RiseType::Pair(_) => Variant::DataName("pair".to_string()),
        RiseType::Index(_) => Variant::DataName("index".to_string()),
        RiseType::Fn(_) => Variant::DataName("fn".to_string()),
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
            (v @ Nat, Nat) | (v @ NatMVar, NatMVar) | (v @ DataMVar, DataMVar) => (v, false, false),

            (Nat, NatMVar) => (Nat, false, true),
            (NatMVar, Nat) => (Nat, true, false),

            (DataName(s), DataMVar) => (DataName(s), false, true),
            (DataMVar, DataName(s)) => (DataName(s), true, false),

            (DataName(s1), DataName(s2)) => {
                if s1 == s2 {
                    (DataName(s1.clone()), false, false)
                } else {
                    self.found_err = Err(format!("merge conflict: {a:?} {b:?}"));
                    (DataName(s1.clone()), false, false)
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
            let added = egraph.add(RiseType::Num(c));
            egraph.union(id, added);
        }
    }
}

fn is_mvar(l: &RiseType) -> bool {
    match l {
        RiseType::NatMVar(_) | RiseType::DataMVar(_) => true,
        _ => false,
    }
}

fn pretty_mvar(egraph: &EGraph, l: &RiseType) -> Option<String> {
    let prefix = match l {
        RiseType::NatMVar(_) => Some("nat_"),
        RiseType::DataMVar(_) => Some("data_"),
        _ => None,
    }?;
    let x = l.children().get(0)?;
    match egraph[*x].nodes.get(0)? {
        RiseType::Symbol(s) => Some(format!("({prefix}mvar {s})")),
        _ => None,
    }
}

struct CostFn;
impl CostFunction<RiseType> for CostFn {
    type Cost = i32;
    fn cost<C>(&mut self, enode: &RiseType, mut costs: C) -> Self::Cost
    where
        C: FnMut(Id) -> Self::Cost,
    {
        let op_cost = match enode {
            RiseType::NatMVar(_) => 100,
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
        let a: RecExpr<RiseType> = (format!("(~ {s1} {s2})")).parse().unwrap();
        let _ = eg.add_expr(&a);
    }

    // run
    let mut runner: Runner<RiseType, UnifyAnalysis> =
        Runner::default().with_egraph(eg).run(&dt_rules());

    #[cfg(feature = "dot")]
    runner.egraph.dot().to_svg("target/foo.svg").unwrap();

    // let s3: Pattern<RiseType> = "(~ ?a ?b)".parse().unwrap();
    // let p = s3.search(&runner.egraph);
    // for m in p {
    //     for s in m.substs {
    //         let id_a = s["?a".parse().unwrap()];
    //         let id_b = s["?b".parse().unwrap()];
    //         let v = runner.egraph[id_a].data.variant.clone();
    //         if v == Variant::Nat || v == Variant::NatMVar {
    //             continue;
    //         }
    //         if id_a != id_b {
    //             return Err(format!(
    //                 "not all data-unifications point to same eclass! {id_a} {id_b}"
    //             ));
    //         }
    //     }
    // }

    runner = Runner::default()
        .with_egraph(runner.egraph)
        .run(&nat_rules_isolate());

    let eg = runner.egraph;

    #[cfg(feature = "dot")]
    eg.dot().to_svg("target/foo.svg").unwrap();
    // #[cfg(feature = "dot")]
    // dbg!(eg.dump());

    let _ = &eg.analysis.found_err.clone()?;

    for class in eg.classes() {
        check_no_self_loops(&eg, class)?
    }

    let s3: Pattern<RiseType> = "(~ (nat_mvar ?a) ?b)".parse().unwrap();
    let mut neweg = EGraph::new(UnifyAnalysis::default());
    let p = s3.search(&eg);
    for m in p {
        for s in m.substs {
            let pid_a = s["?a".parse().unwrap()];
            let a = get_repr(&eg, pid_a);
            let r = RecExpr::from(vec![a.clone(), RiseType::NatMVar(0.into())]);
            let id_a = neweg.add_expr(&r);

            let b = &get_repr_recexpr(&eg, s["?b".parse().unwrap()]);
            let id_b = neweg.add_expr(b);
            neweg.union(id_a, id_b);
        }
    }

    let mut map = HashMap::new();
    let s4: Pattern<RiseType> = "(~ (data_mvar ?a) ?b)".parse().unwrap();
    let p = s4.search(&eg);
    for m in p {
        for s in m.substs {
            let pid_a = s["?a".parse().unwrap()];
            let a = get_repr(&eg, pid_a);
            let r = RecExpr::from(vec![a.clone(), RiseType::DataMVar(0.into())]);
            let id_a = neweg.add_expr(&r);

            let b = &get_repr_recexpr(&eg, s["?b".parse().unwrap()]);
            let id_b = neweg.add_expr(b);
            neweg.union(id_a, id_b);
        }
    }

    // it seems the env is not read when running via lake, so we can't configure iters like this...
    // let iters = std::env::var("EGG_SIMP_ITERS")
    //     .unwrap_or("3".into())
    //     .parse::<usize>()
    //     .expect("cant parse usize in iters");

    let simp_iters = 3;

    let runner: Runner<RiseType, UnifyAnalysis> = Runner::default()
        .with_egraph(neweg)
        // .with_scheduler(SimpleScheduler {})
        .with_iter_limit(simp_iters)
        // .with_time_limit(Duration::from_secs(5))
        .run(&nat_rules());

    let eg = runner.egraph;
    // #[cfg(feature = "dot")]
    // eg.dot().to_svg("target/foo.svg").unwrap();

    // dbg!(eg.dump());
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

    Ok(map)
}

fn get_repr_recexpr(eg: &EGraph, id: Id) -> RecExpr<RiseType> {
    let init = get_repr(&eg, id);
    let repr: RecExpr<RiseType> = init.build_recexpr(|n| get_repr(&eg, n));
    repr
}

fn get_repr(eg: &EGraph, id: Id) -> RiseType {
    let class = eg[id].clone();
    match get_variant(&class.nodes[0]) {
        Variant::Nat | Variant::NatMVar => {
            let ex = Extractor::new(&eg, CostFn {});
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
                _ => non_mvars[0].clone(),
                // _ => {
                //     panic!("found multiple non_mvars: {non_mvars:?}")
                // }
            }
        }
    }
}
