use crate::{Error, ErrorKind};

use super::{*, first_pass::FirstPassData};



pub fn final_pass<'src>(pass_data:&FirstPassData<'src>, domain:&Domain<'src>, problem:&Problem<'src>) -> Result<CompiledProblem<'src>, Error<'src>> {
    let actions = create_concrete_actions(&pass_data, domain)?;
    let init = visit_init(&pass_data, &problem.init)?;
    let mut goal = Vec::with_capacity(32);
    
    visit_precondition(&pass_data, &problem.goal, None, &mut goal)?;
    Ok(CompiledProblem {
        memory_size: pass_data.preprocess.predicate_memory_map.len(),
        actions,
        init,
        goal,
    })
}

/// Action parameters type to object map results in permutations
/// of objects that match given type. When checking if action can
/// be accomplished we need to choose over which actions to perform it.
/// Having one action per concrete object tuple allows us to use the same
/// heuristic to decide if actions over some objects are more likely to
/// accomplish goal than other actions over some objects. Alternative is
/// to have heuristic function advise both order of actions and order of
/// objects.
/// # Arguments
/// * `compiler` - all pre-computed maps maintained by the compiler
/// * `domain` - PDDL Domain that defines all the actions needed to create.
fn create_concrete_actions<'src>(
    pass_data: &FirstPassData<'src>,
    domain: &Domain<'src>,
) -> Result<Vec<CompiledAction<'src>>, Error<'src>> {
    let mut all_actions =
        Vec::with_capacity(pass_data.preprocess.predicate_memory_map.len() * domain.actions.len() / 5);
    for action in &domain.actions {
        if let Action::Basic(action @ BasicAction { parameters, .. }) = action {
            // Create action for all type-object permutations.
            let actions = for_all_type_object_permutations(
                &pass_data.preprocess.type_to_objects_map,
                parameters.as_slice(),
                |args| visit_basic_action(pass_data, Some(args), action),
            )?;
            all_actions.extend(actions)
        } else {
            todo!()
        }
    }
    Ok(all_actions)
}

fn visit_basic_action<'src>(
    pass_data: &FirstPassData<'src>,
    args: Option<&[(&Name<'src>, &Name<'src>)]>,
    action: &BasicAction<'src>,
) -> Result<CompiledAction<'src>, Error<'src>> {
    let mut precondition = Vec::new();
    action
        .precondition
        .as_ref()
        .and_then(|p| Some(visit_precondition(pass_data, p, args, &mut precondition)))
        .unwrap_or(Ok(()))?;
    let mut effect = Vec::new();
    action
        .effect
        .as_ref()
        .and_then(|e| Some(visit_effect(pass_data, e, args, &mut effect)))
        .unwrap_or(Ok(()))?;
    let args: Vec<Name> = if let Some(args) = args {
        args.iter().map(|(_, o)| (**o).clone()).collect()
    } else {
        Vec::new()
    };
    Ok(CompiledAction {
        name: action.name.clone(),
        args,
        precondition,
        effect,
    })
}

fn visit_init<'src>(
    pass_data: &FirstPassData<'src>,
    init: &[Init<'src>],
) -> Result<Vec<Instruction>, Error<'src>> {
    let mut instructions = Vec::with_capacity(32);
    for exp in init {
        match exp {
            Init::AtomicFormula(formula) => {
                instructions.push(Instruction::And(0));
                visit_name_negative_formula(pass_data, formula, &mut instructions)?;
            }
            Init::At(_, _) => todo!(),
            Init::Equals(_, _) => todo!(),
            Init::Is(_, _) => todo!(),
        }
    }
    Ok(instructions)
}

fn visit_term_atomic_formula<'src>(
    pass_data: &FirstPassData<'src>,
    af: &AtomicFormula<'src, Term<'src>>,
    args: Option<&[(&Name<'src>, &Name<'src>)]>,
    instructions: &mut Vec<Instruction>,
    is_effect: bool,
) -> Result<(), Error<'src>> {
    use ErrorKind::{ExpectedName, ExpectedVariable, UndeclaredVariable};
    use super::Term::*;
    match af {
        AtomicFormula::Predicate(name, params) => {
            let mut call_vec = Vec::with_capacity(params.len() + 1);
            call_vec.push(name.1);
            for param in params {
                match param {
                    Variable(var) => {
                        if args.is_none() {
                            return Err(Error {
                                input: None,
                                kind: ExpectedName,
                                chain: None,
                                range: param.range(),
                            });
                        }
                        let args = args.unwrap();
                        let mut is_found = false;
                        for arg in args {
                            if var.1 == arg.0 .1 {
                                call_vec.push(arg.1 .1);
                                is_found = true;
                                break;
                            }
                        }
                        if !is_found {
                            return Err(Error {
                                input: None,
                                kind: UndeclaredVariable,
                                chain: None,
                                range: var.0.clone(),
                            });
                        }
                    }
                    Name(name) => {
                        if args.is_some() {
                            return Err(Error {
                                input: None,
                                kind: ExpectedVariable,
                                chain: None,
                                range: param.range(),
                            });
                        }
                        call_vec.push(name.1);
                    }
                    Function(_) => todo!(),
                }
            }
            if let Some(offset) = pass_data.preprocess.predicate_memory_map.get(&call_vec) {
                instructions.push(if is_effect {
                    Instruction::SetState(*offset)
                } else {
                    Instruction::ReadState(*offset)
                })
            } else {
                panic!("All variables matched, and predicate exists, but can't find this call vec memory offset")
            }
            Ok(())
        }
        AtomicFormula::Equality(_, _) => todo!(),
    }
}

fn visit_name_atomic_formula<'src>(
    pass_data: &FirstPassData<'src>,
    af: &AtomicFormula<'src, Name<'src>>,
    instructions: &mut Vec<Instruction>,
) -> Result<(), Error<'src>> {
    match af {
        AtomicFormula::Predicate(name, args) => {
            let mut call_vec = vec![name.1];
            call_vec.extend(args.iter().map(|a| a.1));
            if let Some(offset) = pass_data.preprocess.predicate_memory_map.get(&call_vec) {
                instructions.push(Instruction::SetState(*offset));
                Ok(())
            } else {
                // Check if predicate is defined, check of object is defined.
                todo!()
            }
        }
        AtomicFormula::Equality(_, _) => todo!(),
    }
}

fn visit_gd<'src>(
    pass_data: &FirstPassData<'src>,
    gd: &GD<'src>,
    args: Option<&[(&Name<'src>, &Name<'src>)]>,
    instructions: &mut Vec<Instruction>,
) -> Result<(), Error<'src>> {
    match gd {
        GD::AtomicFormula(af) => {
            visit_term_atomic_formula(pass_data, af, args, instructions, false)
        }
        GD::And(vec) => {
            for gd in vec {
                visit_gd(pass_data, gd, args, instructions)?
            }
            Ok(())
        }
        GD::Or(_) => todo!(),
        GD::Not(gd) => {
            visit_gd(pass_data, gd, args, instructions)?;
            instructions.push(Instruction::Not);
            Ok(())
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

fn visit_precondition<'src>(
    pass_data: &FirstPassData<'src>,
    precondition: &PreconditionExpr<'src>,
    args: Option<&[(&Name<'src>, &Name<'src>)]>,
    instructions: &mut Vec<Instruction>,
) -> Result<(), Error<'src>> {
    match precondition {
        PreconditionExpr::And(vec) => {
            for preconditions in vec {
                visit_precondition(pass_data, preconditions, args, instructions)?
            }
            instructions.push(Instruction::And(vec.len()));
            Ok(())
        }
        PreconditionExpr::Forall(_) => todo!(),
        PreconditionExpr::Preference(_) => todo!(),
        PreconditionExpr::GD(gd) => visit_gd(pass_data, gd, args, instructions),
    }
}

fn visit_term_negative_formula<'src>(
    pass_data: &FirstPassData<'src>,
    formula: &NegativeFormula<'src, Term<'src>>,
    args: Option<&[(&Name<'src>, &Name<'src>)]>,
    instructions: &mut Vec<Instruction>,
    is_effect: bool,
) -> Result<(), Error<'src>> {
    match formula {
        NegativeFormula::Direct(af) => {
            visit_term_atomic_formula(pass_data, af, args, instructions, is_effect)
        }
        NegativeFormula::Not(af) => {
            if is_effect {
                instructions.push(Instruction::Not);
            }
            visit_term_atomic_formula(pass_data, af, args, instructions, is_effect)?;
            if !is_effect {
                instructions.push(Instruction::Not);
            }
            Ok(())
        }
    }
}

fn visit_name_negative_formula<'src>(
    pass_data: &FirstPassData<'src>,
    formula: &NegativeFormula<'src, Name<'src>>,
    instructions: &mut Vec<Instruction>,
) -> Result<(), Error<'src>> {
    match formula {
        NegativeFormula::Direct(af) => visit_name_atomic_formula(pass_data, af, instructions),
        NegativeFormula::Not(af) => {
            instructions.push(Instruction::Not);
            visit_name_atomic_formula(pass_data, af, instructions)
        }
    }
}

fn visit_fexp<'src>(
    _: &FirstPassData<'src>,
    fexp: &FluentExpression<'src>,
    instructions: &mut Vec<Instruction>,
) -> Result<(), Error<'src>> {
    match fexp {
        FluentExpression::Number(n) => instructions.push(Instruction::Push(*n)),
        FluentExpression::Subtract(_) => todo!(),
        FluentExpression::Negate(_) => todo!(),
        FluentExpression::Divide(_) => todo!(),
        FluentExpression::Add(_) => todo!(),
        FluentExpression::Multiply(_) => todo!(),
        FluentExpression::Function(_) => todo!(),
    }
    Ok(())
}

enum SupportedFunctionOp {
    INC,
}
fn function_op<'src>(
    pass_data: &FirstPassData<'src>,
    function: &FunctionTerm<'src>,
    fexp: &FluentExpression<'src>,
    op: SupportedFunctionOp,
    instructions: &mut Vec<Instruction>,
) -> Result<(), Error<'src>> {
    visit_fexp(pass_data, fexp, instructions)?;
    if function.terms.len() == 0
        && function.name.1 == "total-cost"
        && pass_data.preprocess.requirements.contains(Requirement::ActionCosts)
    {
        use SupportedFunctionOp::*;
        instructions.push(Instruction::ReadFunction(0)); // todo! map functions
        match op {
            INC => instructions.push(Instruction::Add),
        }
        instructions.push(Instruction::SetFunction(0));
        Ok(())
    } else {
        Err(Error {
            input: None,
            kind: ErrorKind::UnsetRequirement(Requirement::ActionCosts.into()),
            chain: None,
            range: function.range(),
        })
    }
}

fn visit_effect<'src>(
    pass_data: &FirstPassData<'src>,
    effect: &Effect<'src>,
    args: Option<&[(&Name<'src>, &Name<'src>)]>,
    instructions: &mut Vec<Instruction>,
) -> Result<(), Error<'src>> {
    match effect {
        Effect::And(vec) => {
            for effect in vec {
                visit_effect(pass_data, effect, args, instructions)?
            }
            Ok(())
        }
        Effect::Forall(_) => todo!(),
        Effect::When(_) => todo!(),
        Effect::NegativeFormula(f) => {
            instructions.push(Instruction::And(0));
            visit_term_negative_formula(pass_data, f, args, instructions, true)
        }
        Effect::Assign(_, _) => todo!(),
        Effect::AssignTerm(_, _) => todo!(),
        Effect::AssignUndefined(_) => todo!(),
        Effect::ScaleUp(_, _) => todo!(),
        Effect::ScaleDown(_, _) => todo!(),
        Effect::Increase(function, fexp) => function_op(
            pass_data,
            function,
            &fexp.1,
            SupportedFunctionOp::INC,
            instructions,
        ),
        Effect::Decrease(_, _) => todo!(),
    }
}

#[cfg(test)]
mod test {

}