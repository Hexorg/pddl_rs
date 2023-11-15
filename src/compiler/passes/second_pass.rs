use std::collections::HashMap;

use crate::{
    compiler::{
        action_graph::ActionGraph, inertia::Inertia, AtomicFormula, BasicAction, CompiledAction,
        CompiledProblem, FunctionTerm, Instruction, Name, PredicateUsize, StateUsize, Term,
    },
    Error,
};

use super::{
    visit_all_actions, visit_effect, visit_init, visit_precondition, AstKind, Compiler, Context,
    ContextPass,
};

pub struct SecondPassContext<'src> {
    pub predicate_memory_map: HashMap<AtomicFormula<'src, Name<'src>>, StateUsize>,
    pub memory_map: Vec<AtomicFormula<'src, Name<'src>>>,
    pub skipped_instructions: PredicateUsize,
    pub instructions: Vec<Instruction>,
    pub inertia: Vec<Inertia<'src, Name<'src>>>,
    pub compiled_problem: CompiledProblem<'src>,
}

impl<'src> SecondPassContext<'src> {
    pub fn new(variable_inertia: Vec<Inertia<'src, Term<'src>>>) -> Self {
        Self {
            skipped_instructions: 0,
            predicate_memory_map: HashMap::new(),
            memory_map: Vec::new(),
            instructions: Vec::new(),
            inertia: Vec::new(),
            compiled_problem: CompiledProblem {
                memory_size: 0,
                constants_size: 0,
                domain_action_ranges: Vec::new(),
                actions: Vec::new(),
                init: Vec::new(),
                goal: Vec::new(),
                action_graph: ActionGraph::new(variable_inertia),
            },
        }
    }
}

pub fn second_pass<'src, 'ast>(
    compiler: &Compiler<'ast, 'src>,
    context: &mut Context<'src>,
) -> Result<(), Vec<Error>>
where
    'ast: 'src,
{
    let pass2_data = context.pass.unwrap_pass2_context();
    for predicate in &compiler.pass1_data.variable_predicates {
        pass2_data.predicate_memory_map.insert(
            predicate.clone(),
            pass2_data.predicate_memory_map.len() as StateUsize,
        );
        pass2_data.memory_map.push(predicate.clone());
    }

    let actions = visit_all_actions(compiler, context)?;
    context.ast_kind = AstKind::Init;
    visit_init(compiler, &compiler.problem.init, context)?;

    let pass2_data = context.pass.unwrap_pass2_context();
    let init = std::mem::take(&mut pass2_data.instructions);
    context.ast_kind = AstKind::Goal;
    visit_precondition(compiler, &compiler.problem.goal, None, context)?;
    let pass2_data = context.pass.unwrap_pass2_context();
    let goal = std::mem::take(&mut pass2_data.instructions);
    let problem = &mut pass2_data.compiled_problem;
    problem.memory_size = compiler.pass1_data.variable_predicates.len() as StateUsize;
    problem.constants_size = (compiler.pass1_data.true_predicates.len()
        + compiler.pass1_data.false_predicates.len()) as StateUsize;
    problem.actions = actions;
    problem.init = init;
    problem.goal = goal;
    problem.action_graph.apply_inertia(&pass2_data.inertia);
    problem.action_graph.apply_dijkstra();
    Ok(())
}

pub fn visit_basic_action<'src, 'ast>(
    compiler: &Compiler<'src, 'ast>,
    action: &BasicAction<'src>,
    args: &[(Name<'src>, (u16, u16))],
    context: &mut Context<'src>,
) -> Result<Option<CompiledAction>, Error> {
    if let Some(precondition) = &action.precondition {
        context.ast_kind = AstKind::Precondition;
        if !visit_precondition(compiler, precondition, Some(args), context)? {
            context.pass.unwrap_pass2_context().instructions.clear();
            return Ok(None);
        }
    }
    let precondition = std::mem::take(&mut context.pass.unwrap_pass2_context().instructions);
    if let Some(effect) = &action.effect {
        context.ast_kind = AstKind::Effect;
        visit_effect(compiler, effect, args, context)?;
    }
    let pass = context.pass.unwrap_pass2_context();
    let effect = std::mem::take(&mut pass.instructions);
    // let mut args_map = HashMap::with_capacity(args.len());
    let mut args_vec = Vec::new();
    for arg in args {
        // args_map.insert(arg.0, arg.1);
        args_vec.push(arg.1);
    }
    // pass.args_map.push(args_map);
    let inertia = pass.compiled_problem.action_graph.variable_inertia
        [context.domain_action_idx as usize]
        .concrete(compiler.problem, args);
    pass.inertia.push(inertia);
    Ok(Some(CompiledAction {
        domain_action_idx: context.domain_action_idx,
        args: args_vec,
        precondition,
        effect,
    }))
}

pub fn visit_term_formula<'src, 'ast>(
    compiler: &Compiler<'src, 'ast>,
    _term_formula: &AtomicFormula<'src, Term<'src>>,
    _args: Option<&[(Name<'src>, (u16, u16))]>,
    context: &mut Context<'src>,
    formula: AtomicFormula<'src, Name<'src>>,
) -> Result<bool, Error> {
    let pass = match &mut context.pass {
        ContextPass::Second(pass) => pass,
        _ => panic!(),
    };
    if let Some(offset) = pass.predicate_memory_map.get(&formula) {
        match context.ast_kind {
            AstKind::Precondition | AstKind::Goal => {
                pass.instructions.push(Instruction::ReadState(*offset))
            }
            AstKind::Effect | AstKind::Init => {
                pass.instructions.push(Instruction::SetState(*offset))
            }
            _ => panic!(),
        }
        Ok(true)
    } else {
        if context.is_negative {
            if compiler.pass1_data.false_predicates.contains(&formula) {
                pass.skipped_instructions += 1;
                Ok(true)
            } else {
                Ok(false)
            }
        } else {
            if compiler.pass1_data.true_predicates.contains(&formula) {
                pass.skipped_instructions += 1;
                Ok(true)
            } else {
                Ok(false)
            }
        }
    }
}

pub fn increate_function_term<'ast, 'src>(
    _compiler: &Compiler<'ast, 'src>,
    fterm: &FunctionTerm<'src>,
    context: &mut Context<'src>,
) -> Result<(), Error> {
    if fterm.name.1 == "total-cost" && fterm.terms.len() == 0 {
        if let ContextPass::Second(pass) = &mut context.pass {
            pass.instructions.push(Instruction::ReadFunction(0));
            pass.instructions.push(Instruction::Add);
            pass.instructions.push(Instruction::SetFunction(0));
        }
    } else {
        todo!()
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use crate::{
        compiler::{maps::map_objects, passes::Compiler, Runnable},
        lib_tests::load_repo_pddl,
        ReportPrinter,
    };

    #[test]
    #[ignore = "Manual trigger for experimentation"]
    fn print_compiled_problem() {
        let sources = load_repo_pddl(
            "sample_problems/barman/domain.pddl",
            "sample_problems/barman/problem_5_10_7.pddl",
        );
        // let sources = load_repo_pddl("sample_problems/simple_domain.pddl", "sample_problems/simple_problem.pddl");
        let (domain, problem) = sources.parse();
        let maps = map_objects(&domain, &problem).unwrap();
        let mut compiler = Compiler::new(&domain, &problem, maps);
        let c_problem = compiler.compile().unwrap_or_print_report(&sources);
        println!("Memory size: {} bits", c_problem.memory_size);
        println!("Constants size: {} bits", c_problem.constants_size);
        println!("Actions: {}", c_problem.actions.len());
        for (_action_idx, action) in c_problem.actions.iter().enumerate() {
            println!(
                "  {}:",
                domain.actions[action.domain_action_idx as usize].name()
            );
            println!(
                "    if {} effect: {}",
                action.precondition.decomp(&compiler.maps.memory_map),
                action.effect.decomp(&compiler.maps.memory_map)
            );
        }
        println!("Action graph:\n{:?}", c_problem.action_graph);
    }
}
