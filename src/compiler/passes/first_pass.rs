use std::collections::HashSet;

use crate::{Error, ErrorKind::*, compiler::{CompiledActionUsize, CompiledAction, BasicAction, ASTActionUsize, inertia, AtomicFSkeleton, action_graph::ActionGraph}};

use super::{AtomicFormula, Name, super::inertia::Inertia, Term, Compiler, Context, AstKind, visit_precondition, visit_all_actions, visit_init, ContextPass, visit_effect};

pub struct FirstPassContext<'src> {
    pub action_pass: ASTActionUsize,
    pub true_predicates:HashSet<AtomicFormula<'src, Name<'src>>>,
    pub false_predicates:HashSet<AtomicFormula<'src, Name<'src>>>,
    pub variable_predicates:HashSet<AtomicFormula<'src, Name<'src>>>,
    pub constant_predicate_names:HashSet<Name<'src>>,
    pub inertia: Vec<Inertia<AtomicFormula<'src, Term<'src>>>>,
    pub action_graph: ActionGraph,
}

impl<'src> FirstPassContext<'src> {
    pub fn new(inertia_size:usize) -> Self {
        Self { 
            action_pass: 0,
            true_predicates: HashSet::new(),
            false_predicates: HashSet::new(),
            variable_predicates: HashSet::new(),
            constant_predicate_names: HashSet::new(),
            inertia: vec![Inertia::new();inertia_size],
            action_graph: ActionGraph::new(),
        }
    }
}

pub fn first_pass<'src, 'ast>(
    compiler: &Compiler<'ast, 'src>,
    context: &mut Context<'src>
)  -> Result<(), Vec<Error>>  where 'ast:'src {
    // Given problem init, only some subset of all action permutations can be created.
    // problem init sets states unconditionally. Action effects set states conditionally.
    // we need to find which states are never set. 
    // We have to iterate over all the actions squared - each time taking note of 
    // true, false, and variable predicates. 

    let pass = context.pass.unwrap_pass1_context();
    for AtomicFSkeleton{name,..} in &compiler.domain.predicates {
        pass.constant_predicate_names.insert(*name);
    }

    // First we set problem-init specific predicates
    context.ast_kind = AstKind::Init;
    visit_init(compiler, &compiler.problem.init, context)?;
    context.ast_kind = AstKind::None;

    // then iterate through all possible permuatations as many times as there are actions 
    // to find which predicates are variable and which are constant.
    visit_all_actions(compiler, context)?;
    let pass = context.pass.unwrap_pass1_context();
    let mut vp = pass.variable_predicates.len();
    let mut tp = pass.true_predicates.len();
    let mut fp = pass.false_predicates.len();
    // I think it's impossible to both - detect variable predicates
    // and detect which actions should be tried first without increasing the loop count
    // and A* will have to do a loop anyway, so it's cheaper to not do it here.
    pass.action_pass += 1;
    for i in 1..compiler.domain.actions.len() {
        visit_all_actions(compiler, context)?;
        let pass = context.pass.unwrap_pass1_context();
        pass.action_pass += 1;

        if pass.variable_predicates.len() == vp && pass.false_predicates.len() == fp && pass.true_predicates.len() == tp {
            // potentially we need to iterate n^2 times, but there's a good chance we finish exploring sooner.
            // all depends on task complexity
            break;
        }
        vp = pass.variable_predicates.len();
        tp = pass.true_predicates.len();
        fp = pass.false_predicates.len();
    }

    // iterate over constant predicates and remove them from inertia

    let pass = context.pass.unwrap_pass1_context();
    for name in &pass.constant_predicate_names {
        for inertia in &mut pass.inertia {
            let mut remove_vec = Vec::with_capacity(pass.true_predicates.len() + pass.false_predicates.len());
            for formula in &inertia.provides_negative {
                if formula.name().1 == name.1 {
                    remove_vec.push(formula.clone());
                }
            }
            for formula in &inertia.provides_positive {
                if formula.name().1 == name.1 {
                    remove_vec.push(formula.clone());
                }
            }
            for formula in &inertia.wants_negative {
                if formula.name().1 == name.1 {
                    remove_vec.push(formula.clone());
                }
            }
            for formula in &inertia.wants_positive {
                if formula.name().1 == name.1 {
                    remove_vec.push(formula.clone());
                }
            }
            for formula in remove_vec {
                inertia.provides_negative.remove(&formula);
                inertia.provides_positive.remove(&formula);
                inertia.wants_negative.remove(&formula);
                inertia.wants_positive.remove(&formula);
            }
        }
    }

    pass.action_graph.apply_inertia(&pass.inertia);
    // pass.action_graph.apply_dijkstra();

    // Sanity check that problem goal is possible
    context.ast_kind = AstKind::Goal;
    if let Err(e) = visit_precondition(compiler, &compiler.problem.goal, None, context) {
        Err(Error{ span: compiler.problem.name.0, kind: UnmetGoal, chain: Some(Box::new(e)) }.into())
    } else {
        Ok(())
    }
}

pub fn visit_basic_action<'src, 'ast>(
    compiler: &Compiler<'src, 'ast>,
    action: &BasicAction<'src>,
    args: &[(Name<'src>, (u16, u16))],
    context: &mut Context<'src>
) -> Result<Option<CompiledAction>, Error> {
    if let Some(precondition) = &action.precondition {
        context.ast_kind = AstKind::Precondition;
        if !visit_precondition(compiler, precondition, Some(args), context)? {
            return Ok(None)
        }
    }


    if let Some(effect) = &action.effect {
        context.ast_kind = AstKind::Effect;
        visit_effect(compiler, effect, args, context)?;
    }
    Ok(None)
}


pub fn visit_term_formula<'src, 'ast>(
    compiler: &Compiler<'src, 'ast>,
    term_formula: &AtomicFormula<'src, Term<'src>>,
    args: Option<&[(Name<'src>, (u16, u16))]>,
    context: &mut Context<'src>,
    formula: AtomicFormula<'src, Name<'src>>,
) -> Result<bool, Error> {
    let pass = match &mut context.pass {
        ContextPass::First(pass) => pass,
        _ => panic!()
    };
    match &context.ast_kind {
        AstKind::Precondition => {
            if pass.variable_predicates.contains(&formula) {
                if context.is_negative {
                    pass.inertia[context.domain_action_idx as usize].wants_negative.insert(term_formula.clone());
                } else {
                    pass.inertia[context.domain_action_idx as usize].wants_positive.insert(term_formula.clone());
                }
                Ok(true)
            } else {
                if context.is_negative {
                    if pass.false_predicates.contains(&formula) {
                        if pass.action_pass == 0 {
                            pass.inertia[context.domain_action_idx as usize].wants_negative.insert(term_formula.clone());
                        }
                        Ok(true)
                    } else {
                        Ok(false)
                    }
                } else {
                    if pass.true_predicates.contains(&formula) {
                        if pass.action_pass == 0 {
                            pass.inertia[context.domain_action_idx as usize].wants_positive.insert(term_formula.clone());
                        }
                        Ok(true)
                    } else {
                        Ok(false)
                    }
                }
            }
        },
        AstKind::Effect => {
            if context.is_negative {
                pass.inertia[context.domain_action_idx as usize].provides_negative.insert(term_formula.clone());
            } else {
                pass.inertia[context.domain_action_idx as usize].provides_positive.insert(term_formula.clone());
            }
            if !pass.variable_predicates.contains(&formula) {
                if context.is_negative {
                    if pass.true_predicates.contains(&formula) {
                        pass.constant_predicate_names.remove(&term_formula.name());
                        pass.true_predicates.remove(&formula);
                        pass.variable_predicates.insert(formula);
                    } else {
                        pass.false_predicates.insert(formula);
                    }
                } else {
                    if pass.false_predicates.contains(&formula) {
                        pass.constant_predicate_names.remove(&term_formula.name());
                        pass.false_predicates.remove(&formula);
                        pass.variable_predicates.insert(formula);
                    } else {
                        pass.true_predicates.insert(formula);
                    }
                }
            } 
            Ok(true)
        },
        AstKind::Goal => {
            if !pass.variable_predicates.contains(&formula) {
                if context.is_negative {
                    if !pass.false_predicates.contains(&formula) {
                        Err(Error{ span:term_formula.name().0, kind: UnmetPredicate, chain: None})
                    } else {
                        Ok(true)
                    }
                } else {
                    if !pass.true_predicates.contains(&formula) {
                        Err(Error{ span:term_formula.name().0, kind: UnmetPredicate, chain: None})
                    } else {
                        Ok(true)
                    }
                }
            } else {
                Ok(true)
            }
        }
        _ => panic!()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{lib_tests::load_repo_pddl, compiler::{maps::map_objects, passes::{Compiler, Context, ContextPass}}, ReportPrinter};

    #[test]
    #[ignore = "Manual trigger for experimentation"]
    fn print_inertia() {
        let sources = load_repo_pddl("sample_problems/barman/domain.pddl", "sample_problems/barman/problem_5_10_7.pddl");
        // let sources = load_repo_pddl("sample_problems/simple_domain.pddl", "sample_problems/simple_problem.pddl");
        let (domain, problem) = sources.parse();
        let maps = map_objects(&domain, &problem).unwrap();
        let compiler = Compiler::new(&domain, &problem, maps);
        let mut context = Context::new(ContextPass::First(FirstPassContext::new(domain.actions.len())));
        first_pass(&compiler, &mut context).unwrap_or_print_report(&sources);
        let context = context.pass.unwrap_pass1_context();
        for i in 0..domain.actions.len() {
            println!("Action {}: {}\n{}", i, domain.actions[i].name(), context.inertia[i]);
        }
        println!("Variable predicates ({}): {:?}", context.variable_predicates.len(), context.variable_predicates);
        println!("True predicates ({}): {:?}", context.true_predicates.len(), context.true_predicates);
        println!("False predicates ({}): {:?}", context.false_predicates.len(), context.false_predicates);
        println!("Fully constant predicates: {:?}", context.constant_predicate_names);
        println!("Action graph:\n{}", context.action_graph);
        for i in 0..domain.actions.len() {
            let vec = context.action_graph.dijkstra(i as CompiledActionUsize);
            print!("Len {}: ", vec.len());
            for action_id in vec {
                print!("{}, ", domain.actions[action_id].name());
            }
            println!()
        }
        context.action_graph.apply_dijkstra();
        println!("Action graph:\n{}", context.action_graph);
    }

    #[test]
    fn test_predicates() {
        let sources = load_repo_pddl("sample_problems/simple_domain.pddl", "sample_problems/simple_problem.pddl");
        let (domain, problem) = sources.parse();
        let maps = map_objects(&domain, &problem).unwrap();
        let compiler = Compiler::new(&domain, &problem, maps);
        let mut context = Context::new(ContextPass::First(FirstPassContext::new(domain.actions.len())));
        first_pass(&compiler, &mut context).unwrap_or_print_report(&sources);
        let context = context.pass.unwrap_pass1_context();
        assert!(context.true_predicates.contains(&AtomicFormula::Predicate(Name::new(0..0, "ball"), vec![Name::new(0..0, "ball1")])));
        assert!(context.true_predicates.contains(&AtomicFormula::Predicate(Name::new(0..0, "ball"), vec![Name::new(0..0, "ball2")])));
        assert!(context.true_predicates.contains(&AtomicFormula::Predicate(Name::new(0..0, "room"), vec![Name::new(0..0, "rooma")])));
        assert!(context.true_predicates.contains(&AtomicFormula::Predicate(Name::new(0..0, "room"), vec![Name::new(0..0, "roomb")])));
        assert!(context.true_predicates.contains(&AtomicFormula::Predicate(Name::new(0..0, "gripper"), vec![Name::new(0..0, "right")])));
        assert!(context.true_predicates.contains(&AtomicFormula::Predicate(Name::new(0..0, "gripper"), vec![Name::new(0..0, "left")])));
        assert_eq!(context.true_predicates.len(), 6);
        assert_eq!(context.false_predicates.len(), 0);
        assert_eq!(context.variable_predicates.len(), 12);
    }

    #[test]
    fn test_inertia() {
        let sources = load_repo_pddl("sample_problems/simple_domain.pddl", "sample_problems/simple_problem.pddl");
        let (domain, problem) = sources.parse();
        let maps = map_objects(&domain, &problem).unwrap();
        let compiler = Compiler::new(&domain, &problem, maps);
        let mut context = Context::new(ContextPass::First(FirstPassContext::new(domain.actions.len())));
        first_pass(&compiler, &mut context).unwrap_or_print_report(&sources);
        let context = context.pass.unwrap_pass1_context();
        assert_eq!(context.inertia.len(), 3);
        assert_eq!(context.inertia[0].wants_positive.len(), 1);
        assert_eq!(context.inertia[0].wants_negative.len(), 0);
        assert_eq!(context.inertia[0].provides_negative.len(), 1);
        assert_eq!(context.inertia[0].provides_positive.len(), 1);
    }
}