use std::{collections::HashMap, path::PathBuf, ops::Range};

use crate::{
    compiler::{
        action_graph::ActionGraph, AtomicFormula, BasicAction, CompiledAction,
        CompiledProblem, Instruction, Name, PredicateUsize, StateUsize, CompiledActionUsize, ASTActionUsize, atomic_formula_map::AtomicFormulaMap,
    },
    Error, parser::ast::{r#type::Type, term::{Term, FunctionTerm}},
};

use super::{
    AstKind, Compiler, Context,
    ContextPass, super::domain::CompiledAtomicFormula,
};

pub struct SecondPassContext {
    /// Maps AtomicFormula<Name> to offset in memory
    pub predicate_memory_map: AtomicFormulaMap,

    pub skipped_instructions: PredicateUsize,
    pub instructions: Vec<Instruction>,
    // pub problem_inertia: Inertia<'src, Name<'src>>,
    pub actions: Vec<CompiledAction>,
    pub domain_action_ranges: Vec<Range<CompiledActionUsize>>,
    pub init: Vec<Instruction>,
    pub goal: Vec<Instruction>,
}

impl SecondPassContext {
    pub fn new() -> Self {
        Self {
            skipped_instructions: 0,
            predicate_memory_map: AtomicFormulaMap::new(),
            instructions: Vec::new(),
            // problem_inertia: Inertia::new(),
            actions: Vec::new(),
            domain_action_ranges: Vec::new(),
            init: Vec::new(),
            goal: Vec::new(),
        }
    }
}

pub fn second_pass<'src, 'ast>(
    compiler: &Compiler<'ast, 'src>,
    context: &mut Context,
) -> Result<(), Vec<Error>>
where
    'ast: 'src,
{
    let pass2_data = context.pass.unwrap_pass2_context();
    for predicate in &compiler.pass1_data.variable_predicates {
        pass2_data.predicate_memory_map.allocate(predicate.clone());
    }

    let actions = compiler.visit_all_actions(context)?;
    context.ast_kind = AstKind::Init;
    compiler.visit_init(&compiler.problem.init, context)?;

    let pass2_data = context.pass.unwrap_pass2_context();
    let init = std::mem::take(&mut pass2_data.instructions);
    pass2_data.init = init;
    context.ast_kind = AstKind::Goal;
    compiler.visit_precondition(&compiler.problem.goal, None, context)?;
    let pass2_data = context.pass.unwrap_pass2_context();
    let goal = std::mem::take(&mut pass2_data.instructions);
    pass2_data.goal = goal;
    pass2_data.actions = actions;
    Ok(())
}

pub fn visit_basic_action<'src, 'ast>(
    compiler: &Compiler<'src, 'ast>,
    action: &'ast BasicAction<'src>,
    args: &[PredicateUsize],
    context: &mut Context,
) -> Result<Option<CompiledAction>, Error> {
    if let Some(precondition) = &action.precondition {
        context.ast_kind = AstKind::Precondition;
        if !compiler.visit_precondition(precondition, Some(args), context)? {
            context.pass.unwrap_pass2_context().instructions.clear();
            return Ok(None);
        }
    }
    let precondition = std::mem::take(&mut context.pass.unwrap_pass2_context().instructions);
    if let Some(effect) = &action.effect {
        context.ast_kind = AstKind::Effect;
        compiler.visit_effect(effect, args, context)?;
    }
    let pass = context.pass.unwrap_pass2_context();
    let effect = std::mem::take(&mut pass.instructions);
    // let mut args_map = HashMap::with_capacity(args.len());

    Ok(Some(CompiledAction {
        domain_action_idx: context.domain_action_idx,
        args: args.to_owned(),
        precondition,
        effect,
    }))
}

pub fn visit_term_formula<'src, 'ast>(
    compiler: &Compiler<'src, 'ast>,
    term_formula: &'ast AtomicFormula<Term<'src>>,
    _args: Option<&[PredicateUsize]>,
    context: &mut Context,
    formula: CompiledAtomicFormula,
) -> Result<bool, Error> {
    let pass = context.pass.unwrap_pass2_context();
    if let Some(offset) = pass.predicate_memory_map.get(&formula) {
        match context.ast_kind {
            AstKind::Precondition =>  {
                pass.instructions.push(Instruction::ReadState(offset));
            },
            AstKind::Goal => { pass.instructions.push(Instruction::ReadState(offset)) }
            AstKind::Effect => {
                pass.instructions.push(Instruction::SetState(offset));
            },
            AstKind::Init => { pass.instructions.push(Instruction::SetState(offset)); }
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
    context: &mut Context,
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
        let compiler = Compiler::new(&domain, &problem, sources.domain_path.clone(), sources.problem_path.clone());
        let c_problem = compiler.compile().unwrap_or_print_report(&sources);
        println!("Action count: {}", c_problem.domain.actions.len());
        println!("Actions permutated with objects count: {}", c_problem.actions.len());
        println!("State space: {} bits", c_problem.memory_size);
        println!("Constants size: {} bits", c_problem.constants_size);
        // println!("Actions: {}", c_problem.actions.len());
        // for (_action_idx, action) in c_problem.actions.iter().enumerate() {
        //     println!(
        //         "  {}:",
        //         domain.actions[action.domain_action_idx as usize].name()
        //     );
        //     println!(
        //         "    if {} effect: {}",
        //         action.precondition.decomp(&c_problem.maps.memory_map),
        //         action.effect.decomp(&c_problem.maps.memory_map)
        //     );
        // }
    }
}
