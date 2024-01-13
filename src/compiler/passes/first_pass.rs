use std::collections::HashSet;

use crate::{
    compiler::{
        ASTActionUsize, AtomicFSkeleton, BasicAction, CompiledAction, PredicateUsize, inertia::ActionInertia, domain::ArgKind, //inertia::ActionInertia,
    },
    Error,
    ErrorKind::{UnmetGoal, UnmetPredicate},
};

use super::{
    super::inertia::Inertia, //visit_all_actions, visit_effect, visit_init, visit_precondition,
    AstKind, AtomicFormula, Compiler, Context, ContextPass, Term, super::domain::CompiledAtomicFormula,
};


pub struct FirstPassContext {
    pub action_pass: ASTActionUsize,
    pub true_predicates: HashSet<CompiledAtomicFormula>,
    pub false_predicates: HashSet<CompiledAtomicFormula>,
    pub variable_predicates: HashSet<CompiledAtomicFormula>,
    pub constant_predicate_idx: HashSet<PredicateUsize>,
    pub inertia: Inertia,
    // pub action_graph: ActionGraph<'src>,
}

impl FirstPassContext {
    pub fn new() -> Self {
        Self {
            action_pass: 0,
            true_predicates: HashSet::new(),
            false_predicates: HashSet::new(),
            variable_predicates: HashSet::new(),
            constant_predicate_idx: HashSet::new(),
            inertia: Inertia::new(),
            // action_graph: ActionGraph::new(Vec::new()),
        }
    }
}

pub fn first_pass<'ast, 'src>(
    compiler: &Compiler<'ast, 'src>,
    context: &mut Context,
) -> Result<(), Vec<Error>>
where
    'ast: 'src,
{
    // Given problem init, only some subset of all action permutations can be created.
    // problem init sets states unconditionally. Action effects set states conditionally.
    // we need to find which states are never set.
    // We have to iterate over all the actions squared - each time taking note of
    // true, false, and variable predicates.

    let pass = context.pass.unwrap_pass1_context();
    for AtomicFSkeleton { name, .. } in &compiler.domain.predicates {
        let predicate_idx = *compiler.maps.predicate_id_map.get(name.1).unwrap();
        pass.constant_predicate_idx.insert(predicate_idx);
    }
    for action in &compiler.domain.actions {
        pass.inertia.actions.push(match action {
            crate::parser::ast::Action::Basic(ba) => ActionInertia::new(&ba.parameters, &compiler.maps),
            crate::parser::ast::Action::Durative(_) => todo!(),
            crate::parser::ast::Action::Derived(_, _) => todo!(),
        });
    }

    // First we set problem-init specific predicates
    context.ast_kind = AstKind::Init;
    compiler.visit_init(&compiler.problem.init, context)?;
    context.ast_kind = AstKind::None;

    // println!("After init, there are {} true and {} false predicates", context.pass.unwrap_pass1_context().true_predicates.len(), context.pass.unwrap_pass1_context().false_predicates.len());


    // then iterate through all possible permuatations as many times as there are actions
    // to find which predicates are variable and which are constant.
    // println!("Action pass 1...");
    compiler.visit_all_actions(context)?;
    // panic!();
    let pass = context.pass.unwrap_pass1_context();
    let mut vp = pass.variable_predicates.len();
    let mut tp = pass.true_predicates.len();
    let mut fp = pass.false_predicates.len();
    // I think it's impossible to both - detect variable predicates
    // and detect which actions should be tried first without increasing the loop count
    // and A* will have to do a loop anyway, so it's cheaper to not do it here.
    pass.action_pass += 1;
    for _ in 1..compiler.domain.actions.len() {
        // println!("Action pass {}...", context.pass.unwrap_pass1_context().action_pass+1);
        compiler.visit_all_actions(context)?;
        let pass = context.pass.unwrap_pass1_context();
        pass.action_pass += 1;

        if pass.variable_predicates.len() == vp
            && pass.false_predicates.len() == fp
            && pass.true_predicates.len() == tp
        {
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
    // for name in &pass.constant_predicate_names {
    //     for inertia in &mut pass.inertia {
    //         let mut remove_vec =
    //             Vec::with_capacity(pass.true_predicates.len() + pass.false_predicates.len());
    //         for formula in &inertia.provides.negative {
    //             if formula.name().1 == name.1 {
    //                 remove_vec.push(formula.clone());
    //             }
    //         }
    //         for formula in &inertia.provides.positive {
    //             if formula.name().1 == name.1 {
    //                 remove_vec.push(formula.clone());
    //             }
    //         }
    //         for formula in &inertia.wants.negative {
    //             if formula.name().1 == name.1 {
    //                 remove_vec.push(formula.clone());
    //             }
    //         }
    //         for formula in &inertia.wants.positive {
    //             if formula.name().1 == name.1 {
    //                 remove_vec.push(formula.clone());
    //             }
    //         }
    //         for formula in remove_vec {
    //             inertia.provides.negative.remove(&formula);
    //             inertia.provides.positive.remove(&formula);
    //             inertia.wants.negative.remove(&formula);
    //             inertia.wants.positive.remove(&formula);
    //         }
    //         // let new_provides.negative: HashSet<_> = inertia.provides.negative.union(&inertia.wants.negative).cloned().collect();
    //         // let new_provides.positive: HashSet<_> = inertia.provides.positive.union(&inertia.provides.positive).cloned().collect();
    //         // inertia.provides.negative = new_provides.negative;
    //         // inertia.provides.positive = new_provides.positive;
    //     }
    // }

    // pass.action_graph.apply_dijkstra();

    // Sanity check that problem goal is possible
    context.ast_kind = AstKind::Goal;
    if let Err(e) = compiler.visit_precondition(&compiler.problem.goal, None, context) {
        Err(Error {
            span: compiler.problem.name.0,
            kind: UnmetGoal,
            chain: Some(Box::new(e)),
        }
        .into())
    } else {
        Ok(())
    }
}

pub fn visit_basic_action<'ast, 'src>(
    compiler: &Compiler<'ast, 'src>,
    action: &'ast BasicAction<'src>,
    args: &[PredicateUsize],
    context: &mut Context,
) -> Result<Option<CompiledAction>, Error> {
    if let Some(precondition) = &action.precondition {
        // print!("Visiting precondition...");
        context.ast_kind = AstKind::Precondition;
        if !compiler.visit_precondition(precondition, Some(args), context)? {
            // println!("Action impossible");
            return Ok(None);
        }
        // println!("[OK]");
    }
    // let pass = context.pass.unwrap_pass1_context();

    if let Some(effect) = &action.effect {
        // println!("Visiting effect");
        context.ast_kind = AstKind::Effect;
        compiler.visit_effect(effect, args, context)?;
    }
    Ok(None)
}

pub fn visit_term_formula<'ast, 'src>(
    compiler: &Compiler<'src, 'ast>,
    term_formula: &AtomicFormula<Term<'src>>,
    args: Option<&[PredicateUsize]>,
    context: &mut Context,
    formula: CompiledAtomicFormula,
) -> Result<bool, Error> {
    let pass = &mut context.pass.unwrap_pass1_context();

    let parameters = match &compiler.domain.actions[context.domain_action_idx as usize] {
        crate::parser::ast::Action::Basic(BasicAction{parameters,..}) => parameters,
        crate::parser::ast::Action::Durative(_) => todo!(),
        crate::parser::ast::Action::Derived(_, _) => todo!(),
    };
    
    match &context.ast_kind {
        AstKind::Precondition => {
            if pass.variable_predicates.contains(&formula) {
                pass.inertia.actions[context.domain_action_idx as usize].insert(false, context.is_negative, &compiler.maps, parameters, term_formula)?;
                Ok(true)
            } else {
                if context.is_negative {
                    if pass.false_predicates.contains(&formula) {
                        // if pass.action_pass == 0 {
                        //     pass.inertia[context.domain_action_idx as usize]
                        //         .wants.negative
                        //         .insert(term_formula.typed(compiler.domain.actions[context.domain_action_idx as usize].parameters())?);
                        // }
                        // println!("!{} is possible", formula.decompile(&compiler.maps));
                        Ok(true)
                    } else {
                        // println!("!{} is impossible", formula.decompile(&compiler.maps));
                        Ok(false)
                    }
                } else {
                    if pass.true_predicates.contains(&formula) {
                        // if pass.action_pass == 0 {
                        //     pass.inertia[context.domain_action_idx as usize]
                        //         .wants.positive
                        //         .insert(term_formula.typed(compiler.domain.actions[context.domain_action_idx as usize].parameters())?);
                        // }
                        // println!("{} is possible", formula.decompile(&compiler.maps));
                        Ok(true)
                    } else {
                        // println!("{} is impossible", formula.decompile(&compiler.maps));
                        Ok(false)
                    }
                }
            }
        }
        AstKind::Effect => {
            pass.inertia.actions[context.domain_action_idx as usize].insert(true, context.is_negative, &compiler.maps, parameters, term_formula)?;
            let predicate_idx = formula.predicate_idx;
            if !pass.variable_predicates.contains(&formula) {
                // println!("Effect {:?} under is_negative=={}", term_formula, context.is_negative);
                if context.is_negative {
                    if pass.true_predicates.contains(&formula) {
                        pass.constant_predicate_idx.remove(&predicate_idx);
                        pass.true_predicates.remove(&formula);
                        pass.variable_predicates.insert(formula);
                    } else {
                        pass.false_predicates.insert(formula);
                    }
                } else {
                    if pass.false_predicates.contains(&formula) {
                        pass.constant_predicate_idx.remove(&predicate_idx);
                        pass.false_predicates.remove(&formula);
                        pass.variable_predicates.insert(formula);
                    } else {
                        pass.true_predicates.insert(formula);
                    }
                }
            }
            if !pass.constant_predicate_idx.contains(&predicate_idx) {
                // pass.inertia.action_provides[context.domain_action_idx as usize].insert(context.is_negative, &compiler.maps, parameters, term_formula)?;
            }
            Ok(true)
        }
        AstKind::Goal => {
            let r = if !pass.variable_predicates.contains(&formula) {
                if context.is_negative {
                    if !pass.false_predicates.contains(&formula) {
                        Err(Error {
                            span: term_formula.name().0,
                            kind: UnmetPredicate,
                            chain: None,
                        })
                    } else {
                        Ok(true)
                    }
                } else {
                    if !pass.true_predicates.contains(&formula) {
                        println!("Variable predicates: {}", pass.variable_predicates.iter().map(|f| f.decompile(&compiler.maps, None, ArgKind::Object)).collect::<Vec<_>>().join(", "));
                        println!("True predicates: {}", pass.true_predicates.iter().map(|f| f.decompile(&compiler.maps, None, ArgKind::Object)).collect::<Vec<_>>().join(", "));
                        println!("Unsat formula: {}", formula.decompile(&compiler.maps, None, ArgKind::Object));
                        Err(Error {
                            span: term_formula.name().0,
                            kind: UnmetPredicate,
                            chain: None,
                        })
                    } else {
                        Ok(true)
                    }
                }
            } else {
                Ok(true)
            };
            pass.inertia.problem_goal.insert(context.is_negative, formula);
            r
        }
        _ => panic!(),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        compiler::{
            maps::map_objects,
            passes::{Compiler, Context, ContextPass},
        },
        lib_tests::load_repo_pddl,
        ReportPrinter,
    };

   
    #[test]
    fn test_predicates() {
        let sources = load_repo_pddl(
            "sample_problems/simple_domain.pddl",
            "sample_problems/simple_problem.pddl",
        );
        let (domain, problem) = sources.parse();
        let compiler = Compiler::new(&domain, &problem, sources.domain_path.clone(), sources.problem_path.clone());
        let mut context = Context::new(ContextPass::First(FirstPassContext::new()));
        first_pass(&compiler, &mut context).unwrap_or_print_report(&sources);
        let context = context.pass.unwrap_pass1_context();
        // assert!(context.true_predicates.contains(&AtomicFormula::Predicate(
        //     Name::new(0..0, "ball"),
        //     vec![Name::new(0..0, "ball1")]
        // )));
        // assert!(context.true_predicates.contains(&AtomicFormula::Predicate(
        //     Name::new(0..0, "ball"),
        //     vec![Name::new(0..0, "ball2")]
        // )));
        // assert!(context.true_predicates.contains(&AtomicFormula::Predicate(
        //     Name::new(0..0, "room"),
        //     vec![Name::new(0..0, "rooma")]
        // )));
        // assert!(context.true_predicates.contains(&AtomicFormula::Predicate(
        //     Name::new(0..0, "room"),
        //     vec![Name::new(0..0, "roomb")]
        // )));
        // assert!(context.true_predicates.contains(&AtomicFormula::Predicate(
        //     Name::new(0..0, "gripper"),
        //     vec![Name::new(0..0, "right")]
        // )));
        // assert!(context.true_predicates.contains(&AtomicFormula::Predicate(
        //     Name::new(0..0, "gripper"),
        //     vec![Name::new(0..0, "left")]
        // )));
        assert_eq!(context.true_predicates.len(), 6);
        assert_eq!(context.false_predicates.len(), 0);
        assert_eq!(context.variable_predicates.len(), 12);
    }


}
