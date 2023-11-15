use crate::{Error, ErrorKind::*};

use super::{
    for_all_type_object_permutations, maps::Maps, ASTActionUsize, AtomicFormula, BasicAction,
    CompiledAction, CompiledActionUsize, CompiledProblem, Domain, Effect, FluentExpression, Init,
    Instruction, Name, NegativeFormula, PreconditionExpr, Problem, StateUsize, Term, GD,
};

mod first_pass;
use first_pass::{first_pass, FirstPassContext};
mod second_pass;
use second_pass::{second_pass, SecondPassContext};

/// Compiler context that gets passed to all AST visitors to keep track of
/// inter-node state as we are traversing the Abstract Systax Tree
#[derive(PartialEq, Eq)]
pub enum AstKind {
    None,
    Precondition,
    Effect,
    Goal,
    Init,
}

pub enum ContextPass<'src> {
    First(FirstPassContext<'src>),
    Second(SecondPassContext<'src>),
}

impl<'src> ContextPass<'src> {
    pub fn unwrap_pass1_context(&mut self) -> &mut FirstPassContext<'src> {
        match self {
            ContextPass::First(data) => data,
            _ => panic!(),
        }
    }

    pub fn unwrap_pass2_context(&mut self) -> &mut SecondPassContext<'src> {
        match self {
            ContextPass::Second(data) => data,
            _ => panic!(),
        }
    }
}

/// Gets passed to all AST visitors to keep track of inter-node state as we are
/// traversing the Abstract Systax Tree
pub struct Context<'src> {
    pub errors: Vec<Error>,
    pub ast_kind: AstKind,
    pub is_negative: bool,
    pub domain_action_idx: ASTActionUsize,
    pub action_idx: CompiledActionUsize,
    pub pass: ContextPass<'src>,
}

impl<'src> Context<'src> {
    pub fn new(pass: ContextPass<'src>) -> Self {
        Self {
            errors: Vec::new(),
            ast_kind: AstKind::None,
            is_negative: false,
            domain_action_idx: 0,
            action_idx: 0,
            pass,
        }
    }
    pub fn get_errors_or_data(self) -> Result<ContextPass<'src>, Vec<Error>> {
        if self.errors.len() > 0 {
            Err(self.errors)
        } else {
            Ok(self.pass)
        }
    }
}

pub struct Compiler<'ast, 'src>
where
    'ast: 'src,
{
    domain: &'ast Domain<'src>,
    problem: &'ast Problem<'src>,
    maps: Maps<'src>,
    pass1_data: FirstPassContext<'src>,
}

impl<'ast, 'src> Compiler<'ast, 'src> {
    pub fn new(domain: &'ast Domain<'src>, problem: &'ast Problem<'src>, maps: Maps<'src>) -> Self {
        Self {
            domain,
            problem,
            maps,
            pass1_data: FirstPassContext::new(domain.actions.len()),
        }
    }
    pub fn compile(&mut self) -> Result<CompiledProblem<'src>, Vec<Error>> {
        let mut context = Context::new(ContextPass::First(FirstPassContext::new(
            self.domain.actions.len(),
        )));
        pass(self, &mut context);

        if let ContextPass::First(pass1_data) = context.get_errors_or_data()? {
            self.pass1_data = pass1_data;
        }
        let mut context = Context::new(ContextPass::Second(SecondPassContext::new(
            std::mem::take(&mut self.pass1_data.inertia),
        )));
        pass(self, &mut context);

        if let ContextPass::Second(pass2_data) = context.get_errors_or_data()? {
            self.maps.memory_map = pass2_data.memory_map;
            // self.maps.args_map = pass2_data.args_map;
            Ok(pass2_data.compiled_problem)
        } else {
            panic!("Context pass enum has changed in the middle of the pass.")
        }
    }
}

fn pass<'src, 'ast>(compiler: &Compiler<'ast, 'src>, context: &mut Context<'src>)
where
    'ast: 'src,
{
    if let Err(e) = match &context.pass {
        ContextPass::First(..) => first_pass(compiler, context),
        ContextPass::Second(..) => second_pass(compiler, context),
    } {
        context.errors.extend(e);
    }
}

fn visit_init<'src, 'ast>(
    compiler: &Compiler<'src, 'ast>,
    init: &[Init<'src>],
    context: &mut Context<'src>,
) -> Result<(), Error> {
    for init in init {
        match init {
            Init::AtomicFormula(formula) => {
                visit_negative_name_formula(compiler, formula, context)?
            }
            Init::At(_, _) => todo!(),
            Init::Equals(_, _) => todo!(),
            Init::Is(_, _) => todo!(),
        }
    }
    Ok(())
}

fn visit_all_actions<'src, 'ast>(
    compiler: &Compiler<'src, 'ast>,
    context: &mut Context<'src>,
) -> Result<Vec<CompiledAction>, Error> {
    let mut action_idx = 0;
    let mut all_actions = Vec::new();
    for (domain_action_idx, action) in compiler.domain.actions.iter().enumerate() {
        context.domain_action_idx = domain_action_idx as ASTActionUsize;
        let start_idx = all_actions.len() as CompiledActionUsize;
        match action {
            super::Action::Basic(action) => {
                all_actions.extend(for_all_type_object_permutations(
                    &compiler.maps.type_to_objects_map,
                    &action.parameters,
                    |args| {
                        context.action_idx = action_idx;
                        let r = visit_basic_action(compiler, action, args, context)?;
                        if r.is_some() {
                            action_idx += 1;
                        }
                        Ok(r)
                    },
                )?);
            }
            super::Action::Durative(_) => todo!(),
            super::Action::Derived(_, _) => todo!(),
        }
        let end_idx = all_actions.len() as CompiledActionUsize;
        if let ContextPass::Second(pass) = &mut context.pass {
            pass.compiled_problem
                .domain_action_ranges
                .push(start_idx..end_idx);
        }
    }
    Ok(all_actions)
}

fn visit_basic_action<'src, 'ast>(
    compiler: &Compiler<'src, 'ast>,
    action: &BasicAction<'src>,
    args: &[(Name<'src>, (u16, u16))],
    context: &mut Context<'src>,
) -> Result<Option<CompiledAction>, Error> {
    match context.pass {
        ContextPass::First(..) => first_pass::visit_basic_action(compiler, action, args, context),
        ContextPass::Second(..) => second_pass::visit_basic_action(compiler, action, args, context),
    }
}

fn visit_effect<'src, 'ast>(
    compiler: &Compiler<'src, 'ast>,
    effect: &Effect<'src>,
    args: &[(Name<'src>, (u16, u16))],
    context: &mut Context<'src>,
) -> Result<(), Error> {
    match effect {
        Effect::And(vec) => {
            for effect in vec {
                visit_effect(compiler, effect, args, context)?;
            }
            Ok(())
        }
        Effect::NegativeFormula(formula) => {
            if !visit_negative_term_formula(compiler, formula, args, context)? {
                panic!("Failed effect application")
            }
            Ok(())
        }
        Effect::Forall(_) => todo!(),
        Effect::When(_) => todo!(),
        Effect::AssignTerm(_, _) => todo!(),
        Effect::AssignUndefined(_) => todo!(),
        Effect::Assign(_, _) => todo!(),
        Effect::ScaleUp(_, _) => todo!(),
        Effect::ScaleDown(_, _) => todo!(),
        Effect::Increase(fterm, fexp) => {
            visit_fluent_expression(compiler, &fexp.1, context)?;
            match context.pass {
                ContextPass::Second(..) => {
                    second_pass::increate_function_term(compiler, fterm, context)
                }
                _ => Ok(()),
            }
        }
        Effect::Decrease(_, _) => todo!(),
    }
}

fn visit_fluent_expression<'src, 'ast>(
    _compiler: &Compiler<'ast, 'src>,
    fexp: &FluentExpression<'src>,
    context: &mut Context<'src>,
) -> Result<(), Error> {
    match fexp {
        FluentExpression::Number(i) => {
            if let ContextPass::Second(pass) = &mut context.pass {
                pass.instructions.push(Instruction::Push(*i));
                Ok(())
            } else {
                Ok(())
            }
        }
        FluentExpression::Subtract(_) => todo!(),
        FluentExpression::Negate(_) => todo!(),
        FluentExpression::Divide(_) => todo!(),
        FluentExpression::Add(_) => todo!(),
        FluentExpression::Multiply(_) => todo!(),
        FluentExpression::Function(_) => todo!(),
    }
}

fn visit_negative_term_formula<'src, 'ast>(
    compiler: &Compiler<'src, 'ast>,
    formula: &NegativeFormula<'src, Term<'src>>,
    args: &[(Name<'src>, (u16, u16))],
    context: &mut Context<'src>,
) -> Result<bool, Error> {
    match formula {
        NegativeFormula::Direct(formula) => {
            visit_term_formula(compiler, formula, Some(args), context)
        }
        NegativeFormula::Not(formula) => {
            let is_negative = context.is_negative;
            context.is_negative = !is_negative;
            if let ContextPass::Second(pass) = &mut context.pass {
                pass.instructions.push(Instruction::Not);
            }
            let r = visit_term_formula(compiler, formula, Some(args), context);
            context.is_negative = is_negative;
            r
        }
    }
}

fn visit_negative_name_formula<'src, 'ast>(
    compiler: &Compiler<'src, 'ast>,
    formula: &NegativeFormula<'src, Name<'src>>,
    context: &mut Context<'src>,
) -> Result<(), Error> {
    match formula {
        NegativeFormula::Direct(formula) => visit_name_formula(compiler, formula, context),
        NegativeFormula::Not(formula) => {
            let is_negative = context.is_negative;
            context.is_negative = !is_negative;
            if let ContextPass::Second(pass) = &mut context.pass {
                pass.instructions.push(Instruction::Not);
            }
            let r = visit_name_formula(compiler, formula, context);
            context.is_negative = is_negative;
            r
        }
    }
}

fn visit_term_formula<'src, 'ast>(
    compiler: &Compiler<'src, 'ast>,
    term_formula: &AtomicFormula<'src, Term<'src>>,
    args: Option<&[(Name<'src>, (u16, u16))]>,
    context: &mut Context<'src>,
) -> Result<bool, Error> {
    let formula = match term_formula.try_into() {
        Ok(v) => v,
        Err(e) => {
            if let Some(args) = args {
                term_formula.concrete(&compiler.problem.objects, args)
            } else {
                return Err(e);
            }
        }
    };
    match context.pass {
        ContextPass::First(..) => {
            first_pass::visit_term_formula(compiler, term_formula, args, context, formula)
        }
        ContextPass::Second(..) => {
            second_pass::visit_term_formula(compiler, term_formula, args, context, formula)
        }
    }
}

fn visit_name_formula<'src, 'ast>(
    compiler: &Compiler<'src, 'ast>,
    formula: &AtomicFormula<'src, Name<'src>>,
    context: &mut Context<'src>,
) -> Result<(), Error> {
    assert!(context.ast_kind == AstKind::Init);
    match &mut context.pass {
        ContextPass::First(pass) => {
            if context.is_negative {
                pass.false_predicates.insert(formula.clone());
            } else {
                pass.true_predicates.insert(formula.clone());
            }
        }
        ContextPass::Second(pass) => {
            if let Some(offset) = pass.predicate_memory_map.get(formula) {
                pass.instructions.push(Instruction::SetState(*offset));
            } else {
                if compiler.pass1_data.true_predicates.contains(formula)
                    || compiler.pass1_data.false_predicates.contains(formula)
                {
                    // nop
                } else {
                    panic!()
                }
            }
        }
    }
    Ok(())
}

fn visit_precondition<'src, 'ast>(
    compiler: &Compiler<'src, 'ast>,
    precondition: &PreconditionExpr<'src>,
    args: Option<&[(Name<'src>, (u16, u16))]>,
    context: &mut Context<'src>,
) -> Result<bool, Error> {
    match precondition {
        PreconditionExpr::And(vec) => {
            let mut accumulator = true;
            let mut old_skipped_instructions = 0;
            if let ContextPass::Second(pass) = &mut context.pass {
                old_skipped_instructions = pass.skipped_instructions;
                pass.skipped_instructions = 0;
            }
            for precondition in vec {
                accumulator &= visit_precondition(compiler, precondition, args, context)?
            }
            if let ContextPass::Second(pass) = &mut context.pass {
                if accumulator {
                    let len = vec.len() as StateUsize - pass.skipped_instructions;
                    if len > 1 {
                        pass.instructions.push(Instruction::And(len))
                    }
                }
                pass.skipped_instructions = old_skipped_instructions;
            }
            Ok(accumulator)
        }

        PreconditionExpr::Forall(_) => todo!(),
        PreconditionExpr::Preference(_) => todo!(),
        PreconditionExpr::GD(gd) => visit_gd(compiler, gd, args, context),
    }
}

fn visit_gd<'src, 'ast>(
    compiler: &Compiler<'src, 'ast>,
    gd: &GD<'src>,
    args: Option<&[(Name<'src>, (u16, u16))]>,
    context: &mut Context<'src>,
) -> Result<bool, Error> {
    match gd {
        GD::AtomicFormula(formula) => visit_term_formula(compiler, formula, args, context),
        GD::And(vec) => {
            let mut accumulator = true;
            let mut old_skipped_instructions = 0;
            if let ContextPass::Second(pass) = &mut context.pass {
                old_skipped_instructions = pass.skipped_instructions;
                pass.skipped_instructions = 0;
            }
            for gd in vec {
                accumulator &= visit_gd(compiler, gd, args, context)?;
            }
            if let ContextPass::Second(pass) = &mut context.pass {
                if accumulator {
                    let len = vec.len() as StateUsize - pass.skipped_instructions;
                    if len > 1 {
                        pass.instructions.push(Instruction::And(len))
                    }
                }
                pass.skipped_instructions = old_skipped_instructions;
            }
            Ok(accumulator)
        }
        GD::Or(_) => todo!(),
        GD::Not(gd) => {
            let is_negative = context.is_negative;
            context.is_negative = !is_negative;
            let r = visit_gd(compiler, gd, args, context);
            if let ContextPass::Second(pass) = &mut context.pass {
                pass.instructions.push(Instruction::Not);
            }
            context.is_negative = is_negative;
            r
        }
        GD::Imply(_) => todo!(),
        GD::Exists(_) => todo!(),
        GD::Forall(_) => todo!(),
        GD::LessThan(_, _) => todo!(),
        GD::LessThanOrEqual(_, _) => todo!(),
        GD::Equal(_, _) => todo!(),
        GD::GreatherThanOrEqual(_, _) => todo!(),
        GD::GreaterThan(_, _) => todo!(),
    }
}

#[cfg(test)]
mod tests {
    use crate::{
        compiler::{maps::map_objects, Runnable},
        lib_tests::load_repo_pddl,
        ReportPrinter,
    };

    use super::Compiler;

    #[test]
    fn test_instructions() {
        let sources = load_repo_pddl(
            "sample_problems/simple_domain.pddl",
            "sample_problems/simple_problem.pddl",
        );
        let (domain, problem) = sources.parse();
        let maps = map_objects(&domain, &problem).unwrap();
        let mut compiler = Compiler::new(&domain, &problem, maps);
        let c_problem = match compiler.compile() {
            Ok(problem) => problem,
            Err(vec) => {
                for e in vec {
                    Err(e.into()).unwrap_or_print_report(&sources)
                }
                panic!()
            }
        };
        assert_eq!(c_problem.actions.len(), 18);
        for action in c_problem.actions {
            println!(
                "{}: precondition: {}, effect: {}",
                domain.actions[action.domain_action_idx as usize].name(),
                action.precondition.disasm(),
                action.effect.disasm()
            );
        }
        // println!("{}", c_problem.actions[0].precondition.disasm());
    }
}
