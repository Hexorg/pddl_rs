use std::path::PathBuf;

use crate::{Error, ErrorKind::{UndefinedPredicate, UndefinedVariable, UndefinedObject, ExpectedName}, parser::ast::{atomic_formula::*, term::Term, list::TypedList}, SpannedAst};

use super::{
    permutate, maps::{Maps, map_objects}, ASTActionUsize, AtomicFormula, BasicAction,
    CompiledAction, CompiledActionUsize, CompiledProblem, Domain, Effect, FluentExpression, Init,
    Instruction, Name, PreconditionExpr, Problem, StateUsize, GD, action_graph::ActionGraph, PredicateUsize, domain::CompiledAtomicFormula, //action_plotter::plot_inertia_enables,
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

pub enum ContextPass {
    First(FirstPassContext),
    Second(SecondPassContext),
}

impl ContextPass {
    pub fn unwrap_pass1_context(&mut self) -> &mut FirstPassContext {
        match self {
            ContextPass::First(data) => data,
            _ => panic!(),
        }
    }

    pub fn unwrap_pass2_context(&mut self) -> &mut SecondPassContext {
        match self {
            ContextPass::Second(data) => data,
            _ => panic!(),
        }
    }
}

/// Gets passed to all AST visitors to keep track of inter-node state as we are
/// traversing the Abstract Systax Tree
pub struct Context {
    pub errors: Vec<Error>,
    pub ast_kind: AstKind,
    pub is_negative: bool,
    pub domain_action_idx: ASTActionUsize,
    pub action_idx: CompiledActionUsize,
    pub pass: ContextPass,
}

impl Context {
    pub fn new(pass: ContextPass) -> Self {
        Self {
            errors: Vec::new(),
            ast_kind: AstKind::None,
            is_negative: false,
            domain_action_idx: 0,
            action_idx: 0,
            pass,
        }
    }
    pub fn get_errors_or_data(self) -> Result<ContextPass, Vec<Error>> {
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
    domain_file_path: PathBuf,
    problem_file_path: PathBuf,
    maps: Maps<'src>,
    pass1_data: FirstPassContext,
}

impl<'ast, 'src> Compiler<'ast, 'src> {
    pub fn new(domain: &'ast Domain<'src>, problem: &'ast Problem<'src>, domain_file_path: PathBuf,
    problem_file_path: PathBuf) -> Self {
        Self {
            domain,
            problem,
            domain_file_path, 
            problem_file_path,
            pass1_data: FirstPassContext::new(),
            maps: Maps::new(),
        }
    }
    pub fn compile(mut self) -> Result<CompiledProblem<'ast, 'src>, Vec<Error>> {
        let maps = map_objects(self.domain, self.problem)?;
        self.maps = maps;
        let mut context = Context::new(ContextPass::First(FirstPassContext::new()));
        self.pass(&mut context);

        if let ContextPass::First(pass1_data) = context.get_errors_or_data()? {
            self.pass1_data = pass1_data;
            // self.pass1_data.inertia.constant_predicates = self.pass1_data.constant_predicate_idx.iter().copied().collect();
            // self.pass1_data.inertia.constant_predicates.sort();
        }
        
        let mut context = Context::new(ContextPass::Second(SecondPassContext::new()));
        self.pass(&mut context);

        if let ContextPass::Second(pass2_data) = context.get_errors_or_data()? {
            let mut p = CompiledProblem {
                memory_size: pass2_data.predicate_memory_map.len() as PredicateUsize,
                constants_size: (self.pass1_data.true_predicates.len()
                + self.pass1_data.false_predicates.len()) as StateUsize,
                actions: pass2_data.actions,
                domain_action_ranges: pass2_data.domain_action_ranges,
                init: pass2_data.init,
                goal: pass2_data.goal,
                inertia: self.pass1_data.inertia,
                constant_predicate_ids: self.pass1_data.constant_predicate_idx,
                action_graph: ActionGraph::new(),
                // domain_inertia: self.pass1_data.inertia,
                // problem_inertia: pass2_data.problem_inertia,
                domain: self.domain,
                problem: self.problem,
                maps: self.maps,
            };
            // let mut action_graph = ActionGraph::new();
            // action_graph.apply_inertia(&p);
            // p.action_graph = action_graph;
            // plot_inertia_enables(self.domain, &p.inertia, &p.maps).unwrap();
            Ok(p)
        } else {
            panic!("Context pass enum has changed in the middle of the pass.")
        }
    }

    fn pass(&self, context: &mut Context)
    {
        if let Err(e) = match &context.pass {
            ContextPass::First(..) => first_pass(self, context),
            ContextPass::Second(..) => second_pass(self, context),
        } {
            context.errors.extend(e);
        }
    }

    fn visit_init(
        &self,
        init: &[Init<'src>],
        context: &mut Context,
    ) -> Result<(), Error> {
        for init in init {
            match init {
                Init::AtomicFormula(formula) => {
                    self.visit_negative_name_formula(formula, context)?
                }
                Init::At(_, _) => todo!(),
                Init::Equals(_, _) => todo!(),
                Init::Is(_, _) => todo!(),
            }
        }
        Ok(())
    }

    fn visit_all_actions(
        &self,
        context: &mut Context,
    ) -> Result<Vec<CompiledAction>, Error> {
        let mut action_idx = 0;
        let mut all_actions = Vec::new();
        for (domain_action_idx, action) in self.domain.actions.iter().enumerate() {
            context.domain_action_idx = domain_action_idx as ASTActionUsize;
            let start_idx = all_actions.len() as CompiledActionUsize;
            match action {
                super::Action::Basic(action) => {
                    // println!("Looking at action {}({:?})", action.name.1, action.parameters);
                    all_actions.extend(permutate(action.parameters.len(),
                    |pos|  {
                        let object_vec =self.maps.type_to_objects_map.get(&action.parameters.get_type(pos).to_id(&self.maps)).unwrap();
                        // println!("Parameter position {} has type {} and it has {} objects: {:?}", pos, action.parameters.get_type(pos), object_vec.len(), object_vec);
                        object_vec.iter().copied()
                    },
                        |args| {
                            // println!("args: {:?}", args);
                            // panic!();
                            context.action_idx = action_idx;
                            let r = self.visit_basic_action(action, args, context)?;
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
                pass.domain_action_ranges
                    .push(start_idx..end_idx);
            }
        }
        Ok(all_actions)
    }

    fn visit_basic_action(
        &self,
        action: &'ast BasicAction<'src>,
        args: &[PredicateUsize],
        context: &mut Context,
    ) -> Result<Option<CompiledAction>, Error> {
        match context.pass {
            ContextPass::First(..) => first_pass::visit_basic_action(self, action, args, context),
            ContextPass::Second(..) => second_pass::visit_basic_action(self, action, args, context),
        }
    }

    fn visit_effect(
        &self,
        effect: &'ast Effect<'src>,
        args: &[PredicateUsize],
        context: &mut Context,
    ) -> Result<(), Error> {
        match effect {
            Effect::And(vec) => {
                for effect in vec {
                    self.visit_effect(effect, args, context)?;
                }
                Ok(())
            }
            Effect::NegativeFormula(formula) => {
                if !self.visit_negative_term_formula( formula, args, context)? {
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
                self.visit_fluent_expression(&fexp.1, context)?;
                match context.pass {
                    ContextPass::Second(..) => {
                        second_pass::increate_function_term(self, fterm, context)
                    }
                    _ => Ok(()),
                }
            }
            Effect::Decrease(_, _) => todo!(),
        }
    }

    fn visit_fluent_expression(
        &self,
        fexp: &FluentExpression<'src>,
        context: &mut Context,
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

    fn visit_negative_term_formula(
        &self,
        formula: &'ast NegativeFormula<Term<'src>>,
        args: &[PredicateUsize],
        context: &mut Context,
    ) -> Result<bool, Error> {
        match formula {
            NegativeFormula::Direct(formula) => {
                self.visit_term_formula(formula, Some(args), context)
            }
            NegativeFormula::Not(formula) => {
                let is_negative = context.is_negative;
                context.is_negative = !is_negative;
                if let ContextPass::Second(pass) = &mut context.pass {
                    pass.instructions.push(Instruction::Not);
                }
                let r = self.visit_term_formula(formula, Some(args), context);
                context.is_negative = is_negative;
                r
            }
        }
    }

    fn visit_negative_name_formula(
        &self,
        formula: &NegativeFormula<Name<'src>>,
        context: &mut Context,
    ) -> Result<(), Error> {
        match formula {
            NegativeFormula::Direct(formula) => self.visit_name_formula(formula, context),
            NegativeFormula::Not(formula) => {
                let is_negative = context.is_negative;
                context.is_negative = !is_negative;
                if let ContextPass::Second(pass) = &mut context.pass {
                    pass.instructions.push(Instruction::Not);
                }
                let r = self.visit_name_formula(formula, context);
                context.is_negative = is_negative;
                r
            }
        }
    }

    fn compile_term_formula(&self, term_formula: &'ast AtomicFormula<'src, Term<'src>>, parameters:Option<&'ast TypedList<'src>>, args: Option<&[PredicateUsize]>) -> Result<CompiledAtomicFormula, Error> {
        match term_formula {
            AtomicFormula::Predicate(predicate, vars) => {
                if let Some(predicate_idx) = self.maps.predicate_id_map.get(predicate.1) {
                    let predicate_idx = *predicate_idx;
                    let mut args_vec = Vec::with_capacity(vars.len());
                    for var in vars.iter() {
                        let var_idx = match var {
                            Term::Variable(var_name) => 
                            if let Some(args) = args {
                                args[parameters.unwrap().find(|n| n.1 == var_name.1).unwrap() as usize]
                            } else {
                                panic!("Variable term formula has no provided args")
                            }
                            Term::Name(name) => if let Some(idx) = self.maps.object_id_map.get(name.1) {
                                *idx
                            } else {
                                return Err(Error{span:name.0, kind:UndefinedObject, chain:None})
                            },
                            Term::Function(_) => todo!(),
                        };
                        args_vec.push(var_idx);
                    }
                    let compiled = CompiledAtomicFormula{predicate_idx, args:args_vec};
                    // println!("Term formula: {:?} compiles to {}", term_formula, compiled.decompile(&self.maps));
                    Ok(compiled)
                } else {
                    return Err(Error{span:predicate.0, kind:UndefinedPredicate, chain:None})
                }
            },
            AtomicFormula::Equality(_, _) => todo!(),
        }
    }

    fn visit_term_formula(
        &self,
        term_formula: &'ast AtomicFormula<'src, Term<'src>>,
        args: Option<&[PredicateUsize]>,
        context: &mut Context,
    ) -> Result<bool, Error> {
        let parameters = match &self.domain.actions[context.domain_action_idx as usize] {
            crate::parser::ast::Action::Basic(ba) => &ba.parameters,
            crate::parser::ast::Action::Durative(_) => todo!(),
            crate::parser::ast::Action::Derived(_, _) => todo!(),
        };
        let formula = self.compile_term_formula(term_formula, Some(parameters), args)?;
        match context.pass {
            ContextPass::First(..) => {
                first_pass::visit_term_formula(self, term_formula, args, context, formula)
            }
            ContextPass::Second(..) => {
                second_pass::visit_term_formula(self, term_formula, args, context, formula)
            }
        }
    }

    fn visit_name_formula(
        &self,
        formula: &AtomicFormula<'src, Name<'src>>,
        context: &mut Context,
    ) -> Result<(), Error> {
        assert!(context.ast_kind == AstKind::Init);

        let c_formula = self.compile_term_formula(&formula.into(), None, None)?;
        match &mut context.pass {
            ContextPass::First(pass) => {
                if context.ast_kind == AstKind::Init {
                    pass.inertia.problem_init.insert(context.is_negative, c_formula.clone());
                } else if context.ast_kind == AstKind::Goal {
                    pass.inertia.problem_goal.insert(context.is_negative, c_formula.clone())
                } else {
                    return Err(Error{span:formula.span(), kind:ExpectedName, chain:None})
                }
                if context.is_negative {
                    pass.false_predicates.insert(c_formula);
                } else {
                    pass.true_predicates.insert(c_formula);
                }
            }
            ContextPass::Second(pass) => {
                if let Some(offset) = pass.predicate_memory_map.get(&c_formula) {
                    pass.instructions.push(Instruction::SetState(offset));
                    // if context.is_negative {
                    //     pass.problem_inertia.provides.negative.insert(formula.clone());
                    // } else {
                    //     pass.problem_inertia.provides.positive.insert(formula.clone());
                    // }
                } else {
                    if self.pass1_data.true_predicates.contains(&c_formula)
                        || self.pass1_data.false_predicates.contains(&c_formula)
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

    fn visit_precondition(
        &self,
        precondition: &'ast PreconditionExpr<'src>,
        args: Option<&[PredicateUsize]>,
        context: &mut Context,
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
                    accumulator &= self.visit_precondition(precondition, args, context)?
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
            PreconditionExpr::GD(gd) => self.visit_gd(gd, args, context),
        }
    }

    fn visit_gd(
        &self,
        gd: &'ast GD<'src>,
        args: Option<&[PredicateUsize]>,
        context: &mut Context,
    ) -> Result<bool, Error> {
        match gd {
            GD::AtomicFormula(formula) => self.visit_term_formula(formula, args, context),
            GD::And(vec) => {
                let mut accumulator = true;
                let mut old_skipped_instructions = 0;
                if let ContextPass::Second(pass) = &mut context.pass {
                    old_skipped_instructions = pass.skipped_instructions;
                    pass.skipped_instructions = 0;
                }
                for gd in vec {
                    accumulator &= self.visit_gd(gd, args, context)?;
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
                let r = self.visit_gd(gd, args, context);
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
        let mut compiler = Compiler::new(&domain, &problem,  sources.domain_path.clone(), sources.problem_path.clone());
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
