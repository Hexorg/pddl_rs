use std::{collections::{HashSet, HashMap}, marker::PhantomData};

use crate::{Error, ErrorKind::*, SpannedAst};

use super::{
    domain_data::DomainData,
    AtomicFSkeleton, AtomicFormula, BasicAction, Domain, Effect, List, Name, NegativeFormula,
    PreconditionExpr, Problem, Term, Type, GD, inertia::Inertia, StateUsize, CompiledActionUsize, for_all_type_object_permutations, Init, CompiledProblem, PredicateUsize, Instruction, CompiledAction, ASTActionUsize, action_graph::ActionGraph,
};

/// Compiler context that gets passed to all AST visitors to keep track of
/// inter-node state as we are traversing the Abstract Systax Tree
#[derive(PartialEq, Eq)]
enum ContextKind {
    None,
    Precondition,
    Effect,
    Goal,
    Init,
}

/// Gets passed to all AST visitors to keep track of inter-node state as we are
/// traversing the Abstract Systax Tree
struct Context<'src> {
    pub errors: Vec<Error>,
    pub kind: ContextKind,
    pub is_negative: bool,
    pub domain_action_idx: ASTActionUsize,
    pub action_idx: CompiledActionUsize,
    // First pass context
    pub true_predicates:HashSet<AtomicFormula<'src, Name<'src>>>,
    pub false_predicates:HashSet<AtomicFormula<'src, Name<'src>>>,
    pub variable_predicates:HashSet<AtomicFormula<'src, Name<'src>>>,
    pub inertia: Vec<Inertia<AtomicFormula<'src, Term<'src>>>>,
    // Second pass context
    pub predicate_memory_map:HashMap<AtomicFormula<'src, Name<'src>>, StateUsize>,
    pub skipped_instructions: PredicateUsize,
    pub instructions: Vec<Instruction>,
    // output
    pub compiled_problem: Option<CompiledProblem>

}

impl<'src> Context<'src> {
    pub fn new() -> Self {
        Self { 
            errors: Vec::new(),
            kind: ContextKind::None,
            is_negative: false,
            domain_action_idx:0,
            action_idx: 0,
            true_predicates: HashSet::new(),
            false_predicates: HashSet::new(),
            variable_predicates: HashSet::new(),
            inertia: Vec::new(),
            skipped_instructions: 0,
            predicate_memory_map: HashMap::new(),
            instructions: Vec::new(),
            compiled_problem: None,
        }
    }
}

pub struct Compiler<'ast, 'src> {
    domain:&'ast Domain<'src>,
    problem:&'ast Problem<'src>,
    maps: DomainData<'src>,
    pass:u8,
}

impl<'ast, 'src> Compiler<'ast, 'src> {
    pub fn new(domain:&'ast Domain<'src>, problem:&'ast Problem<'src>, maps:DomainData<'src>) -> Self {
        Self { domain, problem, maps, pass:0 }
    }
    pub fn compile(&mut self) -> Result<CompiledProblem, Vec<Error>> {
        let mut context = Context::new();
        for i in 0..2 {
            self.pass = i;
            pass(self, &mut context)
        }
        if context.errors.len() > 0 {
            Err(context.errors)
        } else {
            Ok(context.compiled_problem.unwrap())
        }
    }
}

fn pass<'src, 'ast>(
    compiler: &Compiler<'ast, 'src>,
    context: &mut Context<'src>
) where 'ast:'src {
    if let Err(e) = match compiler.pass {
        0 => first_pass(compiler, context),
        1 => second_pass(compiler, context),
        _ => panic!("Unexpected compiler pass")
    } {
        context.errors.push(e);
    }
}

fn first_pass<'src, 'ast>(
    compiler: &Compiler<'ast, 'src>,
    context: &mut Context<'src>
)  -> Result<(), Error>  where 'ast:'src {
    // Given problem init, only some subset of all action permutations can be created.
    // problem init sets states unconditionally. Action effects set states conditionally.
    // we need to find which states are never set. 
    // We have to iterate over all the actions squared - each time taking note of 
    // true, false, and variable predicates. 

    // First we set problem-init specific predicates
    context.kind = ContextKind::Init;
    visit_init(compiler, &compiler.problem.init, context)?;
    context.kind = ContextKind::None;

    // then iterate through all possible permuatations as many times as there are actions 
    // to find which predicates are variable and which are constant.
    for _ in 0..compiler.domain.actions.len() {
        visit_all_actions(compiler, context)?;
    }

    // Sanity check that problem goal is possible
    context.kind = ContextKind::Goal;
    if let Err(e) = visit_precondition(compiler, &compiler.problem.goal, None, context) {
        Err(Error{ span: compiler.problem.name.0, kind: UnmetGoal, chain: Some(Box::new(e)) })
    } else {
        Ok(())
    }
}

fn second_pass<'src, 'ast>(
    compiler: &Compiler<'ast, 'src>,
    context: &mut Context<'src>
) -> Result<(), Error>  where 'ast:'src {
    for predicate in &context.variable_predicates {
        context.predicate_memory_map.insert(predicate.clone(), context.predicate_memory_map.len() as StateUsize);
    }
    let actions = visit_all_actions(compiler, context)?;
    context.kind = ContextKind::Init;
    visit_init(compiler, &compiler.problem.init, context)?;
    let init = std::mem::take(&mut context.instructions);
    context.kind = ContextKind::Goal;
    visit_precondition(compiler, &compiler.problem.goal, None, context)?;
    let goal = std::mem::take(&mut context.instructions);
    context.compiled_problem = Some(CompiledProblem{
        memory_size: context.variable_predicates.len() as StateUsize,
        constants_size: (context.true_predicates.len() + context.false_predicates.len()) as StateUsize,
        actions,
        init,
        goal,
        action_graph: ActionGraph::new(),
    });
    Ok(())
}

fn visit_init<'src, 'ast>(
    compiler: &Compiler<'src, 'ast>,
    init:&[Init<'src>],
    context: &mut Context<'src>
) -> Result<(), Error> {
    for init in init {
        match init {
            Init::AtomicFormula(formula) => visit_negative_name_formula(compiler, formula, context)?,
            Init::At(_, _) => todo!(),
            Init::Equals(_, _) => todo!(),
            Init::Is(_, _) => todo!(),
        }
    }
    Ok(())
}

fn visit_all_actions<'src, 'ast>(
    compiler: &Compiler<'src, 'ast>,
    context:&mut Context<'src>
) -> Result<Vec<CompiledAction>, Error> {
    let mut action_idx = 0;
    let mut all_actions = Vec::new();
    for (domain_action_idx, action) in compiler.domain.actions.iter().enumerate() {
        if context.inertia.len() != compiler.domain.actions.len() {
            context.inertia.push(Inertia::new());
        }
        context.domain_action_idx = domain_action_idx as ASTActionUsize;
    
        match action {
            super::Action::Basic(action) => {
                all_actions.extend(for_all_type_object_permutations(&compiler.maps.type_to_objects_map, &action.parameters, |args| {
                    context.action_idx = action_idx;
                    let r = visit_basic_action(compiler, action, args, context)?;
                    if r.is_some() { 
                        action_idx += 1;
                    }
                    Ok(r)
                })?);
            },
            super::Action::Durative(_) => todo!(),
            super::Action::Derived(_, _) => todo!(),
        }
    }
    Ok(all_actions)
}

fn visit_basic_action<'src, 'ast>(
    compiler: &Compiler<'src, 'ast>,
    action: &BasicAction<'src>,
    args: &[(Name<'src>, (u16, u16))],
    context: &mut Context<'src>
) -> Result<Option<CompiledAction>, Error> {
    match compiler.pass {
        0 => {
            if let Some(precondition) = &action.precondition {
                context.kind = ContextKind::Precondition;
                if !visit_precondition(compiler, precondition, Some(args), context)? {
                    return Ok(None)
                }
            }

            if let Some(effect) = &action.effect {
                context.kind = ContextKind::Effect;
                visit_effect(compiler, effect, args, context)?;
            }
            Ok(None)
        },
        1 => {
            if let Some(precondition) = &action.precondition {
                context.kind = ContextKind::Precondition;
                if !visit_precondition(compiler, precondition, Some(args), context)? {
                    context.instructions.clear();
                    return Ok(None)
                }
            }
            let precondition = std::mem::take(&mut context.instructions);
            if let Some(effect) = &action.effect {
                context.kind = ContextKind::Effect;
                visit_effect(compiler, effect, args, context)?;
            }
            let effect = std::mem::take(&mut context.instructions);
            Ok(Some(CompiledAction{ 
                domain_action_idx: context.domain_action_idx, 
                args: args.iter().map(|(_, p)| *p).collect(), 
                precondition, 
                effect }))

        }
        _ => panic!()
    }
}

fn visit_effect<'src, 'ast>(
    compiler: &Compiler<'src, 'ast>,
    effect: &Effect<'src>, 
    args: &[(Name<'src>, (u16, u16))],
    context: &mut Context<'src>
) -> Result<(), Error> {
    match effect {
        super::Effect::And(vec) => { 
            let old_skipped_instructions = context.skipped_instructions;
            context.skipped_instructions = 0;
            for effect in vec { 
                visit_effect(compiler, effect, args, context)?;
            }
            if compiler.pass == 1{
                context.instructions.push(Instruction::And(vec.len() as StateUsize - context.skipped_instructions));
            }
            context.skipped_instructions = old_skipped_instructions;
            Ok(())
        },
        super::Effect::Forall(_) => todo!(),
        super::Effect::When(_) => todo!(),
        super::Effect::NegativeFormula(formula) => {
            if !visit_negative_term_formula(compiler, formula, args, context)? {
                panic!("Failed effect application")
            }
            Ok(())
        },
        super::Effect::Assign(_, _) => todo!(),
        super::Effect::AssignTerm(_, _) => todo!(),
        super::Effect::AssignUndefined(_) => todo!(),
        super::Effect::ScaleUp(_, _) => todo!(),
        super::Effect::ScaleDown(_, _) => todo!(),
        super::Effect::Increase(_, _) => Ok(()),
        super::Effect::Decrease(_, _) => todo!(),
    }
}

fn visit_negative_term_formula<'src, 'ast>(
    compiler: &Compiler<'src, 'ast>,
    formula: &NegativeFormula<'src, Term<'src>>,
    args: &[(Name<'src>, (u16, u16))],
    context: &mut Context<'src>,
) -> Result<bool, Error> {
    match formula {
        NegativeFormula::Direct(formula) => visit_term_formula(compiler, formula, Some(args), context),
        NegativeFormula::Not(formula) => { 
            let is_negative = context.is_negative;
            context.is_negative = !is_negative;
            let r = visit_term_formula(compiler, formula, Some(args), context);
            context.is_negative = is_negative;
            r
        },
    }
}

fn visit_negative_name_formula<'src, 'ast>(
    compiler: &Compiler<'src, 'ast>,
    formula: &NegativeFormula<'src, Name<'src>>,
    context: &mut Context<'src>,
) -> Result<(), Error> {
    match formula {
        NegativeFormula::Direct(formula) => visit_name_formula(compiler, formula, context),
        NegativeFormula::Not(formula) => { let is_negative = context.is_negative;
            context.is_negative = !is_negative;
            let r = visit_name_formula(compiler, formula, context);
            context.is_negative = is_negative;
            r
        },
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
        Err(e) => if let Some(args) = args { 
            term_formula.concrete(compiler.problem, args) 
        } else { 
            return Err(e); 
        }
    };
    match compiler.pass {
        0 => {
            match context.kind {
                ContextKind::Precondition => {
                    if context.variable_predicates.contains(&formula) {
                        if context.is_negative {
                            context.inertia.last_mut().unwrap().wants_negative.insert(term_formula.clone());
                        } else {
                            context.inertia.last_mut().unwrap().wants_positive.insert(term_formula.clone());
                        }
                        Ok(true)
                    } else {
                        if context.is_negative {
                            Ok(context.false_predicates.contains(&formula))
                        } else {
                            Ok(context.true_predicates.contains(&formula))
                        }
                    }
                },
                ContextKind::Effect => {
                    if !context.variable_predicates.contains(&formula) {
                        if context.is_negative {
                            context.inertia.last_mut().unwrap().provides_negative.insert(term_formula.clone());
                            if context.true_predicates.contains(&formula) {
                                context.true_predicates.remove(&formula);
                                context.variable_predicates.insert(formula);
                            } else {
                                context.false_predicates.insert(formula);
                            }
                        } else {
                            context.inertia.last_mut().unwrap().provides_positive.insert(term_formula.clone());
                            if context.false_predicates.contains(&formula) {
                                context.false_predicates.remove(&formula);
                                context.variable_predicates.insert(formula);
                            } else {
                                context.true_predicates.insert(formula);
                            }
                        }
                    }
                    Ok(true)
                },
                ContextKind::Goal => {
                    if !context.variable_predicates.contains(&formula) {
                        if context.is_negative {
                            if !context.false_predicates.contains(&formula) {
                                Err(Error{ span:term_formula.name().0, kind: UnmetPredicate, chain: None})
                            } else {
                                Ok(true)
                            }
                        } else {
                            if !context.true_predicates.contains(&formula) {
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
        },
        1 => {
            if let Some(offset) = context.predicate_memory_map.get(&formula) {
                match context.kind { 
                    ContextKind::Precondition |
                    ContextKind::Goal => context.instructions.push(Instruction::ReadState(*offset)),
                    ContextKind::Effect |
                    ContextKind::Init => context.instructions.push(Instruction::SetState(*offset)),
                    _ => panic!()
                }
                Ok(true)
            } else {
                if context.is_negative {
                    if context.false_predicates.contains(&formula) {
                        context.skipped_instructions += 1;
                        Ok(true)
                    } else {
                        Ok(false)
                    }
                } else {
                    if context.true_predicates.contains(&formula) {
                        context.skipped_instructions += 1;
                        Ok(true)
                    } else {
                        Ok(false)
                    }
                }
            }
        }
        _ => panic!()
    }
}

fn visit_name_formula<'src, 'ast>(
    compiler: &Compiler<'src, 'ast>,
    formula: &AtomicFormula<'src, Name<'src>>,
    context: &mut Context<'src>,
) -> Result<(), Error> {
    assert!(context.kind == ContextKind::Init);
    match compiler.pass {
        0 => if context.is_negative {
            context.false_predicates.insert(formula.clone());
        } else {
            context.true_predicates.insert(formula.clone());
        },
        _ => (),
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
            let old_skipped_instructions = context.skipped_instructions;
            context.skipped_instructions = 0;
            for precondition in vec { 
                accumulator &= visit_precondition(compiler, precondition, args, context)? 
            } 
            if compiler.pass == 1 && accumulator {
                context.instructions.push(Instruction::And(vec.len() as StateUsize - context.skipped_instructions))
            }
            context.skipped_instructions = old_skipped_instructions;
            Ok(accumulator) 
        },
            
        PreconditionExpr::Forall(_) => todo!(),
        PreconditionExpr::Preference(_) => todo!(),
        PreconditionExpr::GD(gd) => visit_gd(compiler, gd, args, context),
    }
}

fn visit_gd<'src, 'ast>(
    compiler: &Compiler<'src, 'ast>,
    gd: &GD<'src>, 
    args: Option<&[(Name<'src>, (u16, u16))]>,
    context: &mut Context<'src>
) -> Result<bool, Error> {
    match gd {
        GD::AtomicFormula(formula) => visit_term_formula(compiler, formula, args, context),
        GD::And(vec) => { 
            let mut accumulator = true;
            let old_skipped_instructions = context.skipped_instructions;
            context.skipped_instructions = 0;
            for gd in vec { 
                accumulator &= visit_gd(compiler, gd, args, context)?;
            } 
            if compiler.pass == 1 && accumulator {
                context.instructions.push(Instruction::And(vec.len() as StateUsize - context.skipped_instructions))
            }
            context.skipped_instructions = old_skipped_instructions;
            Ok(accumulator)
        },
        GD::Or(_) => todo!(),
        GD::Not(gd) => {
            let is_negative = context.is_negative;
            context.is_negative = !is_negative;
            let r = visit_gd(compiler, gd, args, context);
            context.is_negative = is_negative;
            r
        },
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
    use crate::{lib_tests::load_repo_pddl, compiler::{domain_data::map_objects, AtomicFormula, Name, Runnable}, ReportPrinter};

    use super::{Compiler, Context, first_pass};

    #[test]
    fn test_predicates() {
        let sources = load_repo_pddl("sample_problems/simple_domain.pddl", "sample_problems/simple_problem.pddl");
        let (domain, problem) = sources.parse();
        let maps = map_objects(&domain, &problem).unwrap();
        let compiler = Compiler::new(&domain, &problem, maps);
        let mut context = Context::new();
        first_pass(&compiler, &mut context).unwrap_or_print_report(&sources);
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
        let mut context = Context::new();
        first_pass(&compiler, &mut context).unwrap_or_print_report(&sources);
        // for i in 0..domain.actions.len() {
        //     println!("{}\n{}", domain.actions[i].name(), context.inertia[i]);
        // }
        assert_eq!(context.inertia.len(), 3);
        assert_eq!(context.inertia[0].wants_positive.len(), 1);
        assert_eq!(context.inertia[0].wants_negative.len(), 0);
        assert_eq!(context.inertia[0].provides_negative.len(), 1);
        assert_eq!(context.inertia[0].provides_positive.len(), 1);
    }

    #[test]
    fn test_instructions() {
        let sources = load_repo_pddl("sample_problems/simple_domain.pddl", "sample_problems/simple_problem.pddl");
        let (domain, problem) = sources.parse();
        let maps = map_objects(&domain, &problem).unwrap();
        let mut compiler = Compiler::new(&domain, &problem, maps);
        let c_problem = match compiler.compile() {
            Ok(problem) => problem,
            Err(vec) => { for e in vec { Err(e).unwrap_or_print_report(&sources) } panic!()}
        };
        assert_eq!(c_problem.actions.len(), 18);
        for action in c_problem.actions {
            println!("{}: precondition: {}, effect: {}", domain.actions[action.domain_action_idx as usize].name(), action.precondition.disasm(), action.effect.disasm());
        }
        // println!("{}", c_problem.actions[0].precondition.disasm());
    }
}
