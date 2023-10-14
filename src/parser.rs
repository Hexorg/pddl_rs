pub mod ast;
pub mod input;

use self::{input::Input, ast::ConstraintGD};
use enumset::EnumSet;

use ast::*;

use nom::{self, 
    sequence::{pair, delimited, terminated, preceded, separated_pair, tuple}, 
    combinator::{recognize, map, opt, value}, 
    character::complete::{alpha1, multispace0, digit0, digit1}, 
    Parser, 
    InputTakeAtPosition, 
    branch::alt, 
    multi::{many0, fold_many1}, bytes::complete::is_not, InputLength, number, Err};

use ariadne::{Label, Report, ReportKind};
use std::ops::Range;


#[derive(PartialEq, Clone, Copy, Debug)]
enum ErrorKind<'src> {
    Nom(nom::error::ErrorKind),
    UnsetRequirement(EnumSet<Requirement>),
    Tag(&'src str),
    Many1(&'static str),
    FunctionType,
    Name,
    Variable,
    Parenthesis,
    UnclosedParenthesis,
    TypedList,
    PreconditionExpression,
    Effect,
    FluentExpression,
    GD, 
    Term, 
    FunctionTerm,
    FunctionTypedList,
}

#[derive(PartialEq, Clone, Debug)]
pub struct Error<'src> {
    input:&'src str,
    kind:ErrorKind<'src>,
    chain:Option<Box<Self>>,
    range: Range<usize>,
}
pub struct UnsetRequirementError(EnumSet<Requirement>);

impl<'src> nom::error::FromExternalError<Input<'src>, UnsetRequirementError> for Error<'src> {
    fn from_external_error(input: Input<'src>, kind: nom::error::ErrorKind, e: UnsetRequirementError) -> Self {
        Self{input:input.src, kind:ErrorKind::UnsetRequirement(e.0), chain:None, range:input.range()}
    }
}
impl<'src> nom::error::ParseError<Input<'src>> for Error<'src> {
    fn from_error_kind(input: Input<'src>, kind: nom::error::ErrorKind) -> Self {
        Self{input:input.src, kind:ErrorKind::Nom(kind), chain:None, range:input.range()}
    }

    fn append(input: Input<'src>, kind: nom::error::ErrorKind, other: Self) -> Self {
        Self{input:input.src, kind:ErrorKind::Nom(kind), chain:Some(Box::new(other)), range:input.range()}
    }
}

impl<'src> Error<'src> {
    pub fn unset_requirement(input:Input<'src>, requirements:EnumSet<Requirement>) -> Self {
        Self{input:input.src, kind:ErrorKind::UnsetRequirement(requirements), chain:None, range:input.range()}
    }
}


type IResult<'src, O> = nom::IResult<Input<'src>, O, Error<'src>>;

fn err_name<'src>(ek: ErrorKind<'src>) -> impl FnMut(nom::Err<Error<'src>>) -> nom::Err<Error<'src>> {
    move |e| 
        e.map(|Error{input, chain, range, ..}| {
            let len = match ek {
                ErrorKind::Nom(_) => todo!(),
                ErrorKind::UnsetRequirement(_) => todo!(),
                ErrorKind::Name |
                ErrorKind::Variable |
                ErrorKind::Term |
                ErrorKind::TypedList |
                ErrorKind::FunctionType |
                ErrorKind::GD |
                ErrorKind::PreconditionExpression |
                ErrorKind::FluentExpression |
                ErrorKind::FunctionTypedList |
                ErrorKind::Effect |
                ErrorKind::Tag(_) => input.char_indices().find(|(_, c)| c.is_ascii_whitespace()).and_then(|(p, _)| Some(p)).unwrap_or(0),
                ErrorKind::Many1(_) |
                ErrorKind::FunctionTerm |
                ErrorKind::UnclosedParenthesis|
                ErrorKind::Parenthesis => 1,
            };
            Error{chain, input, kind:ek, range:Range{start:range.start, end:range.start+len}}
    })
}

pub fn map_ok<'src, O, F, G>(mut parser: F, mut f: G) -> impl FnMut(Input<'src>) -> IResult<O>
    where
    F: FnMut(Input<'src>) -> IResult<O>,
    G: FnMut(Input<'src>, O) -> IResult<O> {
    move |input: Input<'src>| {
        let (i, o) = parser.parse(input)?;
        f(i, o)
    }
}


impl<'src> Error<'src> {
    fn make_label(&self, filename:&'static str) -> Label<(&'src str, Range<usize>)> {
        let label = Label::new((filename, self.range.clone()));
        match self.kind {
            ErrorKind::Nom(_) => todo!(),
            ErrorKind::UnsetRequirement(r) => label.with_message(format!("Unset requirements {:#?}.", r)),
            ErrorKind::Tag(name) => label.with_message(format!("Expected keyword {}.", name)),
            ErrorKind::Many1(name) => label.with_message(format!("Expected one or more {}.", name)),
            ErrorKind::FunctionType => todo!(),
            ErrorKind::Name => todo!(),
            ErrorKind::Variable => todo!(),
            ErrorKind::Parenthesis => todo!(),
            ErrorKind::UnclosedParenthesis => todo!(),
            ErrorKind::TypedList => todo!(),
            ErrorKind::PreconditionExpression => todo!(),
            ErrorKind::Effect => todo!(),
            ErrorKind::FluentExpression => todo!(),
            ErrorKind::GD => todo!(),
            ErrorKind::Term => label.with_message("Expected name, variable, or function term if :object-fluents is set."),
            ErrorKind::FunctionTerm => todo!(),
            ErrorKind::FunctionTypedList => todo!(),
        }
    }
    pub fn report(&self, filename:&'static str) -> Report<'src, (&'src str, Range<usize>)> {
        let report = Report::<'src, (&'src str, Range<usize>)>::build(ReportKind::Error, filename, self.range.start);
        let mut report = report.with_message("Parse error");
        report.add_label(self.make_label(filename));
        let mut cerror = self;
        while let Some(e) = cerror.chain.as_ref() {
            cerror = e.as_ref();
            report.add_label(cerror.make_label(filename));
        }
        report.finish()
    }
}

fn ignore<'src>(input: Input<'src>) -> IResult<()> {
    value((), multispace0.and(opt(pair(char(';'), is_not("\n")))).and(multispace0))(input)
}

fn tag<'src>(tag_name:&'src str) -> impl Parser<Input<'src>, (), Error<'src>> {
    value((), terminated(
        move |i|nom::bytes::complete::tag(tag_name)(i).map_err(err_name(ErrorKind::Tag(tag_name))), 
        ignore
    ))
}

fn many1<'src, O, G>(parser:G, name:&'static str) -> impl FnMut(Input<'src>) -> IResult<Vec<O>> 
where 
    O:'src,
    G: FnMut(Input<'src>)->IResult<O>+Copy {
        move |i:Input<'src>|nom::multi::many1(parser)(i).map_err(err_name(ErrorKind::Many1(name)))
    }

fn minus_separated(input:Input) -> IResult<Spanned<char>> {
    delimited(multispace0, char('-'), multispace0)(input)
}

pub fn preceded_span_included<'src, O1, O2, F, G>(mut first: F, mut second: G) -> impl FnMut(Input<'src>) -> IResult<O2>
    where
    O1:SpannedAst + 'src,
    O2:SpannedAstMut + 'src,
    F: Parser<Input<'src>, O1, Error<'src>>,
    G: Parser<Input<'src>, O2, Error<'src>> {
    move |input:Input<'src>| {
        let origin = input.input_pos;
        let (input, _) = first.parse(input)?;
        let (input, mut o2) = second.parse(input)?;
        o2.range_mut().start = origin;
        Ok((input, o2))
    }
}

pub fn char(c: char) -> impl Fn(Input) -> IResult<Spanned<char>> {
    move |i| nom::character::complete::char(c)(i).map(|(i, o)| {let end = i.input_pos; (i, (Range{start:end-1, end}, o))})
}

// pub fn delimited<'src, O1, O2, O3, F, G, H>(mut first: F, mut second: G, mut third: H) -> impl FnMut(Input<'src>) -> IResult<O2>
//   where
//   O1:SpannedAst + 'src,
//   O2:SpannedAstMut + 'src,
//   O2:SpannedAst,
//   F: Parser<Input<'src>, O1, Error<'src>>,
//   G: Parser<Input<'src>, O2, Error<'src>>,
//   H: Parser<Input<'src>, O3, Error<'src>> {
//     move |input: Input<'src>| {
//       let (input, _) = first.parse(input)?;
//       let (input, o2) = second.parse(input)?;
//       third.parse(input).map(|(i, _)| (i, o2))
//     }
//   }

fn parens<'src, O2, G>(parser:G) -> impl FnMut(Input<'src>) -> IResult<O2> 
where 
    G: Parser<Input<'src>, O2, Error<'src>> {
    delimited(|i|char('(')(i).map_err(err_name(ErrorKind::Parenthesis)), 
        parser, 
        terminated(|i|char(')')(i).map_err(err_name(ErrorKind::UnclosedParenthesis)), multispace0))
}

fn pddl_anyletter(input: Input) -> IResult<Input> {
    input.split_at_position_complete(|c| !(c.is_ascii_alphanumeric() || c == '_' || c == '-'))
}

// // ******************
// // ******************
// // ******************
// // ******************
// // ******************
pub fn parse_domain<'src>(src:&'src str, input_pos:usize) -> IResult<Domain<'src>> {
    let input = Input{src, input_pos, requirements:EnumSet::EMPTY};
    map(parens(tuple((
        tag("define"),
        parens(pair(tag("domain"), name)),
        opt(require_def),
        opt(types_def),
        opt(constants_def),
        opt(predicates_def),
        opt(functions_def),
        opt(constraints),
        many0(structure_def)
    ))), |((), ((), name), requirements, types, constants, predicates, functions, constraints, actions)| 
    Domain{ name, 
        requirements: requirements.unwrap_or_default(), 
        types: types.unwrap_or_default(), 
        constants: constants.unwrap_or_default(), 
        predicates: predicates.unwrap_or_default(), 
        functions: functions.unwrap_or_default(), 
        constraints, 
        actions
    })(input)
}

fn require_def(input:Input) -> IResult<EnumSet<Requirement>> {
    parens(preceded(
        tag(":requirements"), 
        fold_many1(require_key, || EnumSet::EMPTY, |acc,kind| acc | kind)
    ))(input).map(|(mut i, o)| {i.requirements = o; (i, o)})
}

fn require_key(input:Input) -> IResult<Requirement> {
    alt((
        map(tag(":strips"), |_|Requirement::Strips),
        map(tag(":typing"), |_|Requirement::Typing),
        map(tag(":negative-preconditions"), |_|Requirement::NegativePreconditions),
        map(tag(":disjunctive-preconditions"), |_|Requirement::DisjunctivePreconditions),
        map(tag(":equality"), |_|Requirement::Equality),
        map(tag(":existential-preconditions"), |_|Requirement::ExistentialPreconditions),
        map(tag(":universal-preconditions"), |_|Requirement::UniversalPreconditions),
        map(tag(":conditional-effects"), |_|Requirement::ConditionalEffects),
        map(tag(":fluents"), |_|Requirement::ObjectFluents),
        map(tag(":numeric-fluents"), |_|Requirement::NumericFluents),
        map(tag(":durative-actions"), |_|Requirement::DurativeActions),
        map(tag(":duration-inequalities"), |_|Requirement::DurationInequalities),
        map(tag(":continuous-effects"), |_|Requirement::ContinuousEffects),
        map(tag(":derived-predicates"), |_|Requirement::DerivedPredicates),
        map(tag(":timed-initial-literals"), |_|Requirement::TimedInitialLiterals),
        map(tag(":preferences"), |_|Requirement::Preferences),
        map(tag(":constraints"), |_|Requirement::Constraints),
        map(tag(":action-costs"), |_|Requirement::ActionCosts),
    ))(input) 
}

fn types_def(input:Input) -> IResult<Vec<List>> {
    if input.requirements.contains(Requirement::Typing) {
        parens(preceded(
            tag(":types"), 
            many1(|input| typed_list(name, input), "typed list of names")
        ))(input)
    } else {
        Err(nom::Err::Failure(Error::unset_requirement(input, Requirement::Typing.into())))
    }
}

fn constants_def(input:Input) -> IResult<Vec<List>> {
    parens(preceded(
        tag(":constants"), 
        many1(|input| typed_list(name, input), "typed list of names")
    ))(input)
}

fn predicates_def(input:Input) -> IResult<Vec<AtomicFSkeleton>> {
    parens(preceded(
        tag(":predicates"), 
        many1(atomic_function_skeleton, "atomic function skeleton")
    ))(input)
}

use name as predicate;

fn variable(input:Input) -> IResult<Name> {
    preceded_span_included(char('?'), name)(input).map_err(err_name(ErrorKind::Variable))

}


fn atomic_function_skeleton(input: Input) -> IResult<AtomicFSkeleton> {
    parens(pair(
        function_symbol, 
        many1(|input| typed_list(variable, input), "typed list of variables")
    )).map(|(name, variables)| AtomicFSkeleton{name, variables}).parse(input)
}

use name as function_symbol;

fn functions_def(input:Input) -> IResult<Vec<FunctionTypedList>> {
    if input.requirements.is_superset(Requirement::ObjectFluents | Requirement::NumericFluents) {
        parens(preceded(
            tag(":functions"), 
            many1(function_typed_list, "function typed list")
        ))(input)
    } else {
        Err(nom::Err::Failure(Error::unset_requirement(input, Requirement::ObjectFluents | Requirement::NumericFluents)))
    }
}

fn function_typed_list(input:Input) -> IResult<FunctionTypedList> {
    let requirements = input.requirements;
    let result = map(pair(many1(atomic_function_skeleton, "atomic function skeleton"), 
        preceded(minus_separated, function_type)
    ), |(functions, kind)| FunctionTypedList{functions, kind})(input.clone());
    if let Err(nom::Err::Error(Error{chain, input:src,..})) = result {
        if requirements.contains(Requirement::NumericFluents) {
            many1(atomic_function_skeleton, "atomic function skeleton").map(|functions| FunctionTypedList{functions, kind:FunctionType::None})
                .parse(input).map_err(err_name(ErrorKind::FunctionTypedList))
        } else {
            Err(nom::Err::Error(Error{chain, input:src, kind:ErrorKind::FunctionTypedList, range:Range{start:0, end:1}}))
        }
    } else {
        result
    }
}

fn function_type(input:Input) -> IResult<FunctionType> {
    if input.requirements.contains(Requirement::NumericFluents) {
        map(digit0, |o:Input| FunctionType::Numeric((Range{start:o.input_pos, end:o.input_pos+o.input_len()}, i64::from_str_radix(o.src, 10).unwrap())))(input).map_err(err_name(ErrorKind::FunctionType))
    } else if input.requirements.is_superset(Requirement::Typing | Requirement::ObjectFluents) {
        map(r#type, |t| FunctionType::Typed(t))(input).map_err(err_name(ErrorKind::FunctionType))
    } else {
         Err(nom::Err::Error(Error{
            input:input.src, 
            kind:ErrorKind::UnsetRequirement(Requirement::Typing | Requirement::ObjectFluents),
            chain:None,
            range:Range { start: 0, end:1 }
        }))
    }
}

fn constraints(input:Input) -> IResult<ConstraintGD> {
    if input.requirements.contains(Requirement::Constraints) {
        parens(preceded(
            tag(":constraints"), 
            con_gd
        ))(input)
    } else {
        Err(nom::Err::Failure(Error::unset_requirement(input, Requirement::Constraints.into())))
    }
}

fn structure_def(input:Input) -> IResult<Action> {
    alt((
        map(action_def, |a| Action::Basic(a)),
        map(durative_action_def, |a| Action::Durative(a)),
        // map(derived_def, |a| Action::Derived(a))
    ))(input)
}


fn typed_list<'src, G>(parser:G, input:Input<'src>) -> IResult<List> 
where 
    G: FnMut(Input<'src>) -> IResult<Name<'src>> +Copy {
        let r = input.requirements;
        let input_pos = input.input_pos;
        let result = alt((
            map_ok(map(separated_pair(many1(parser, "name or variable"), minus_separated, r#type), |(items, kind)| List{items, kind}), 
                |i, o| if r.contains(Requirement::Typing) { 
                    Ok((i, o)) 
                } else { 
                    Err(nom::Err::Failure(Error{
                        input:input.src, 
                        kind: ErrorKind::UnsetRequirement(Requirement::Typing.into()), 
                        chain:None, 
                        range: Range{start:input_pos, end:i.input_pos} 
                    }))
                }),
            map(many1(parser, "name or variable"), |items| List{items, kind:Type::None})

        ))(input).map_err(err_name(ErrorKind::TypedList));
        result
}

use name as primitive_type;

fn r#type(input:Input) -> IResult<Type> {
    alt((
        map(primitive_type, |o| Type::Exact(o)),
        map(preceded(delimited(multispace0, tag("either"), multispace0), many1(primitive_type, "primitive type")), |vec| Type::Either(vec))
    ))(input)
}

fn empty_or<'src, O2, G>(parser:G) -> impl FnMut(Input<'src>) -> IResult<Option<O2>> 
where 
    O2: 'src,
    G: FnMut(Input<'src>) -> IResult<O2>+Copy {
    alt((
        map(tag("()"), |_| None),
        map(parser, |p| Some(p))
    ))
}

fn action_def(input:Input) -> IResult<BasicAction> {
    map(parens(tuple((
        preceded(tag(":action"), action_symbol),
        preceded(tag(":parameters"), parens(many1(|input| typed_list(variable, input), "typed list of variables"))),
        map(opt(preceded(tag(":precondition"), empty_or(pre_gd))), |o| o.and_then(|f| f)),
        map(opt(preceded(tag(":effect"), empty_or(effect))), |o| o.and_then(|f| f)),
    ))), |(name, parameters, precondition, effect)| BasicAction{name, parameters, precondition, effect})(input)
}

fn forall<'src, O2, G>(parser:G) -> impl FnMut(Input<'src>) -> IResult<Forall<O2>> 
where 
    O2: 'src,
    G: FnMut(Input<'src>) -> IResult<O2>+Copy {
        parens(preceded(
            tag("forall"), 
            map(pair(
                parens(many1(move |input| typed_list(variable, input), "typed list")),
                parser
            ), |(variables, gd)| Forall{variables, gd:Box::new(gd)})
        ))
}

fn exists<'src, O2, G>(parser:G) -> impl FnMut(Input<'src>) -> IResult<Exists<O2>> 
where 
    O2: 'src,
    G: FnMut(Input<'src>) -> IResult<O2>+Copy {
        parens(preceded(
            tag("exists"), 
            map(pair(
                parens(many1(move |input| typed_list(variable, input), "typed list")),
                parser
            ), |(variables, gd)| Forall{variables, gd:Box::new(gd)})
        ))
}

fn preference<'src, O2, G>(parser:G) -> impl FnMut(Input<'src>) -> IResult<Preference<O2>> 
where 
    O2: 'src,
    G: FnMut(Input<'src>) -> IResult<O2> {
        parens(preceded(
            tag("preference"), 
            map(pair(
                opt(pref_name),
                parser
            ), |(name, gd)| Preference{name, gd})
        ))
}

fn pre_gd(input:Input) -> IResult<PreconditionExpr> {
    alt((
        map(parens(preceded(tag("and"), many0(pre_gd))), |vec| PreconditionExpr::And(vec)),
        map(forall(pre_gd), |forall| PreconditionExpr::Forall(forall)),
        map(preference(gd), |pref| PreconditionExpr::Preference(pref)),
        map(gd, |gd| PreconditionExpr::GD(gd)),
    ))(input).map_err(err_name(ErrorKind::PreconditionExpression))
}

use name as pref_name;

fn gd(input:Input) -> IResult<GD> {
    alt((
        map(atomic_formula(term), |af| GD::AtomicFormula(af)),
        map(literal(term), |lit| match lit { 
            NegativeFormula::Direct(af) => GD::AtomicFormula(af),
            NegativeFormula::Not(af) => GD::Not(Box::new(GD::AtomicFormula(af)))
        }),
        map(parens(preceded(tag("and"), many0(gd))), |gd| GD::And(gd)),
        map(parens(preceded(tag("or"), many0(gd))), |gd| GD::Or(gd)),
        map(parens(preceded(tag("not"), gd)), |gd| GD::Not(Box::new(gd))),
        map(parens(preceded(tag("imply"), pair(gd, gd))), |t| GD::Imply(Box::new(t))),
        map(exists(gd), |e| GD::Exists(e)),
        map(forall(gd), |f| GD::Forall(f)),
   ))(input).map_err(err_name(ErrorKind::GD))
}
use name as action_symbol;

fn literal<'src, O2, G>(parser:G) -> impl FnMut(Input<'src>) -> IResult<NegativeFormula<O2>> 
where 
    O2:'src,
    G: Copy+FnMut(Input<'src>) -> IResult<O2> {
        alt((
            map(parens(preceded(tag("not"), atomic_formula(parser))), |af| NegativeFormula::Not(af)),
            map(atomic_formula(parser), |af| NegativeFormula::Direct(af))
        ))
}

fn atomic_formula<'src, O2, G>(parser:G) -> impl FnMut(Input<'src>) -> IResult<AtomicFormula<O2>> 
where 
    O2: 'src,
    G: FnMut(Input<'src>) -> IResult<O2>+Copy {
        alt((
            map(parens(pair(predicate, many0(parser))), |(predicate, vec)| AtomicFormula::Predicate(predicate, vec)),
            map(parens(preceded(tag("="), pair(parser, parser))), |(left, right)| AtomicFormula::Equality(left, right))
        ))
}

fn term(input:Input) -> IResult<Term> {
    alt((
        variable.map(|o| Term::Variable(o)),
        name.map(|o| Term::Name(o)), 
        function_term.map(|o| Term::Function(o)),
    ))(input).map_err(err_name(ErrorKind::Term))
}

fn function_term(input:Input) -> IResult<FunctionTerm> {
    if input.requirements.contains(Requirement::ObjectFluents) {
        parens(pair(function_symbol, many0(term)))
        .map(|(name, terms)| { let mut span = terms.range(); span.start = name.0.start; FunctionTerm{span, name, terms}}).parse(input).map_err(err_name(ErrorKind::FunctionTerm))
    } else {
        Err(nom::Err::Error(Error::unset_requirement(input, EnumSet::EMPTY | Requirement::ObjectFluents)))
    }
}

fn f_exp(input:Input) -> IResult<Spanned<FluentExpression>> {
    alt((
        map(digit0, |o:Input| {let src = o.src; (o.into(), FluentExpression::Number(i64::from_str_radix(src, 10).unwrap()))}),
        map(parens(preceded(tag("-"), f_exp)), |(r, args)| (r.clone(), FluentExpression::Negate(Box::new((r, args))))),
        map(parens(preceded(tag("-"), pair(f_exp, f_exp))), |args| (Range{start:args.0.0.start, end:args.1.0.end}, FluentExpression::Subtract(Box::new(args)))),
        map(parens(preceded(tag("/"), pair(f_exp, f_exp))), |args| (Range{start:args.0.0.start, end:args.1.0.end}, FluentExpression::Divide(Box::new(args)))),
        map(parens(preceded(tag("+"), many1(f_exp, "fluent expression"))), |args| (args.range(), FluentExpression::Add(args))),
        map(parens(preceded(tag("*"), many1(f_exp, "fluent expression"))), |args| (args.range(), FluentExpression::Multiply(args))),
        map(f_head, |f| (f.span.clone(), FluentExpression::Function(f)))
    ))(input).map_err(err_name(ErrorKind::FluentExpression))
}

fn f_head(input:Input) -> IResult<FunctionTerm> {
    alt((
        function_term,
        map(function_symbol, |name| FunctionTerm{span:name.range(), name, terms:Vec::new()})
    ))(input)
}

fn name(input:Input) -> IResult<Name> {
    terminated(
        map(recognize(pair(alpha1, pddl_anyletter)), |o| (Range{start:o.input_pos, end:o.input_pos+o.src.len()}, o.src)),
        ignore
    )(input).map_err(err_name(ErrorKind::Name))
}

fn effect(input:Input) -> IResult<Effect> {
    alt((
        map(parens(preceded(tag("and"), many0(effect))), |vec| Effect::And(vec)),
        map(forall(effect), |forall| Effect::Forall(forall)),
        map(parens(preceded(tag("when"), pair(gd, effect))), |(gd, effect)| Effect::When(When{gd, effect:Box::new(effect)})),
        map(literal(term), |l| Effect::NegativeFormula(l)),
        map(parens(preceded(tag("scale-up"), pair(f_head, f_exp))), |(t, e)| Effect::ScaleUp(t, e)),
        map(parens(preceded(tag("scale-down"), pair(f_head, f_exp))), |(t, e)| Effect::ScaleDown(t, e)),
        map(parens(preceded(tag("increase"), pair(f_head, f_exp))), |(t, e)| Effect::Increase(t, e)),
        map(parens(preceded(tag("decrease"), pair(f_head, f_exp))), |(t, e)| Effect::Decrease(t, e)),
        map(parens(preceded(tag("assign"), pair(f_head, f_exp))), |(t, e)| Effect::Assign(t, e)),
        map(parens(preceded(tag("assign"), pair(function_term, term))), |(t, e)| Effect::AssignTerm(t, e)),
        map(parens(preceded(tag("assign"), pair(f_head, tag("undefined")))), |(t, _)| Effect::AssignUndefined(t)),
    ))(input).map_err(err_name(ErrorKind::Effect))
}

fn durative_action_def(input:Input) -> IResult<DurativeAction> {
    map(parens(tuple((
        tag(":durative-action"),
        da_symbol,
        tag(":parameters"),
        parens(many1(|i|typed_list(variable, i), "variable typed list")),
        tag(":duration"),
        duration_contraint,
        tag(":condition"),
        empty_or(da_gd),
        tag(":effect"),
        empty_or(da_effect)
    ))), |((), name, (), parameters, (), duration, (), condition, (), effect)| DurativeAction{ name, 
        parameters, 
        duration, 
        condition, 
        effect})(input)
}

use name as da_symbol;

fn da_gd(input:Input) -> IResult<DurationGD> {
    alt((
        map(timed_gd, |tgd| DurationGD::GD(tgd)),
        map(preference(timed_gd), |pref| DurationGD::Preference(pref)),
        map(parens(preceded(tag("and"), many0(da_gd))), |vec| DurationGD::And(vec)),
        map(forall(da_gd), |forall| DurationGD::Forall(forall)),
    ))(input)
}

fn timed_gd(input:Input) -> IResult<TimedGD> {
    parens(alt((
        map(pair(tag("at start"), gd), |((), gd)| TimedGD::AtStart(gd)),
        map(pair(tag("at end"), gd), |((), gd)| TimedGD::AtEnd(gd)),
        map(pair(tag("over all"), gd), |((), gd)| TimedGD::OverAll(gd))
    )))(input)
}

fn duration_contraint(input:Input) -> IResult<DurationConstraint> {
    parens(alt((
        map(pair(tag("and"), many0(duration_contraint)), |((), vec)| DurationConstraint::And(vec)),
        map(tag("()"), |_| DurationConstraint::None),
        map(pair(tag("<= ?duration"), f_exp), |((), exp)| DurationConstraint::LessThanOrEquals(exp)),
        map(pair(tag(">= ?duration"), f_exp), |((), exp)| DurationConstraint::GreaterOrEquals(exp)),
        map(pair(tag("= ?duration"), f_exp), |((), exp)| DurationConstraint::Equals(exp)),
        map(pair(tag("at start"), duration_contraint), |((), d)| DurationConstraint::AtStart(Box::new(d))),
        map(pair(tag("at end"), duration_contraint), |((), d)| DurationConstraint::AtEnd(Box::new(d))),
    )))(input)
}

fn da_effect(input:Input) -> IResult<DurationEffect> {
    parens(alt((
        map(pair(tag("and"), many0(da_effect)), |((), vec)| DurationEffect::And(vec)),
        map(timed_effect, |gd| DurationEffect::GD(gd)),
        map(forall(da_effect), |forall| DurationEffect::Forall(forall)),
        map(parens(preceded(tag("when"), pair(da_gd, timed_effect))), |(gd, effect)| DurationEffect::When(When{gd, effect:Box::new(effect)})),
    )))(input)
}

fn timed_effect(input:Input) -> IResult<TimedEffect> {
    alt((
        map(pair(tag("at start"), effect), |((), e)| TimedEffect::AtStart(e)),
        map(pair(tag("at end"), effect), |((), e)| TimedEffect::AtEnd(e)),
        map(effect, |e| TimedEffect::Effect(e))
    ))(input)
}

pub fn parse_problem<'src>(src:&'src str, input_pos:usize, requirements:EnumSet<Requirement>) -> IResult<Problem<'src>> {
    let input = Input{src, input_pos, requirements};
    map(parens(tuple((
        tag("define"),
        parens(pair(tag("problem"), name)),
        parens(pair(tag(":domain"), name)),
        opt(require_def),
        opt(parens(pair(tag(":objects"), many1(|i|typed_list(name, i), "typed list of names")))),
        opt(parens(pair(tag(":init"), many0(init_el)))),
        parens(pair(tag(":goal"), pre_gd)),
        opt(parens(pair(tag(":constraints"), pref_con_gd))),
        opt(parens(pair(tag(":metric"), metric_spec)))
    ))), |((), ((), name), ((), domain), requirements, objects, init, ((), goal), constraints, metric)| {
    let requirements = requirements.unwrap_or(EnumSet::EMPTY);
    let objects = objects.and_then(|((), o)| Some(o)).unwrap_or_default();
    let init = init.and_then(|((), o)| Some(o)).unwrap_or_default();
    let constraints = constraints.and_then(|((), o)| Some(o));
    let metric = metric.and_then(|((), o)| Some(o));
    Problem{ name,
        domain,
        requirements,
        objects,
        init,
        goal,
        constraints,
        metric,
    }})(input)
}

fn init_el(input:Input)->IResult<Init> {
    alt((
        map(literal(name), |l| Init::AtomicFormula(l)),
        map(parens(tuple((tag("at"), digit1, literal(name)))),
            |((), Input{src,..}, literal)| Init::At(i64::from_str_radix(src, 10).unwrap(), literal)),
        map(parens(tuple((tag("="), function_term, digit1))), |((), term, Input{src,..})| Init::Equals(term, i64::from_str_radix(src, 10).unwrap())),
        map(parens(tuple((tag("="), function_term, name))), |((), term, name)| Init::Is(term, name))
    ))(input)
}

fn pref_con_gd(input:Input) -> IResult<PrefConstraintGD> {
    alt((
        map(parens(pair(tag("and"), many0(pref_con_gd))), |((), vec)| PrefConstraintGD::And(vec)),
        map(forall(pref_con_gd), |forall| PrefConstraintGD::Forall(forall)),
        map(preference(con_gd), |pref| PrefConstraintGD::Preference(pref)),
        map(con_gd, |gd| PrefConstraintGD::GD(gd))
    ))(input)
}

fn con_gd(input:Input) -> IResult<ConstraintGD> {
    alt((
        map(parens(preceded(tag("and"), many0(con_gd))), |f| ConstraintGD::And(f)),
        map(forall(con_gd), |forall| ConstraintGD::Forall(forall)),
        map(pair(tag("at end"), gd), |((), gd)| ConstraintGD::AtEnd(gd)),
        map(pair(tag("always"), gd), |((), gd)| ConstraintGD::Always(gd)),
        map(pair(tag("sometime"), gd), |((), gd)| ConstraintGD::Sometime(gd)),
        map(tuple((tag("within"), digit1, gd)), |((), number, gd)| ConstraintGD::Within(i64::from_str_radix(number.src, 10).unwrap(), gd)),
        map(pair(tag("at-most-once"), gd), |((), gd)| ConstraintGD::AtMostOnce(gd)),
        map(tuple((tag("sometime-after"), gd, gd)), |((), left, right)| ConstraintGD::SometimeAfter(left, right)),
        map(tuple((tag("sometime-before"), gd, gd)), |((), left, right)| ConstraintGD::SometimeBefore(left, right)),
        map(tuple((tag("always-within"), digit1, gd, gd)), |((), number, left, right)| ConstraintGD::AlwaysWithin(i64::from_str_radix(number.src, 10).unwrap(), left, right)),
        map(tuple((tag("hold-during"), digit1, digit1, gd)), |((), val, res, gd)| ConstraintGD::HoldDuring(i64::from_str_radix(val.src, 10).unwrap(), i64::from_str_radix(res.src, 10).unwrap(), gd)),
        map(tuple((tag("hold-after"), digit1, gd)), |((), number, gd)| ConstraintGD::HoldAfter(i64::from_str_radix(number.src, 10).unwrap(), gd))
    ))(input)
}

fn metric_spec(input:Input) -> IResult<Metric> {
    alt((
        map(pair(tag("minimize"), metric_f_exp), |((), mfe)| Metric::Minimize(mfe)),
        map(pair(tag("maximize"), metric_f_exp), |((), mfe)| Metric::Maximize(mfe)),
    ))(input)
}

fn metric_f_exp(input:Input) -> IResult<MetricFluentExpr> {
    alt((
        map(tag("total-time"), |_| MetricFluentExpr::TotalTime()),
        map(parens(pair(tag("is-violated"), name)), |((), name)| MetricFluentExpr::IsViolated(name)),
        map(f_exp, |f| MetricFluentExpr::FExpr(f))
    ))(input)
}

#[cfg(test)]
mod tests {
    use ariadne::Source;

    use super::*;

    #[test]
    fn test_basic() {
        assert_eq!(pddl_anyletter(Input::new("H_ i")), 
            Ok((Input{src:" i", input_pos:2, requirements:EnumSet::EMPTY}, 
                Input::new("H_")
        )));
        assert_eq!(name(Input::new("He-l_lo world")), 
            Ok((Input{src:"world", input_pos:8, requirements:EnumSet::EMPTY}, 
            (Range{start:0, end:7}, "He-l_lo")
        )));
        assert_eq!(name(Input::new("#$Hello")), 
            Err(nom::Err::Error(Error{input:"#$Hello", kind:ErrorKind::Name, chain:None, range:Range { start: 0, end: 0 }}))
        );
        assert_eq!(variable(Input::new("?test me")), 
            Ok((Input{src:"me", input_pos:6, requirements:EnumSet::EMPTY}, 
            (Range{start:0, end:5},"test")
        )));

        assert_eq!(pair(name, variable)(Input::new("hello ?world")), 
            Ok((Input{src:"", input_pos:12, requirements:EnumSet::EMPTY}, ((Range{start:0, end:5}, "hello"), (Range{start:6, end:12}, "world")))));

        assert_eq!(term(Input{src:"(test ?one)  ", input_pos:0, requirements:Requirement::ObjectFluents.into()}), 
            Ok((Input{src:"", input_pos:13, requirements:Requirement::ObjectFluents.into()}, 
            Term::Function(FunctionTerm{span:Range{start:1, end:10}, name:(Range{start:1, end:5}, "test"), terms:vec![Term::Variable((Range{start:6, end:10}, "one"))]})
        )));
        let test = Error{input:"(test ?one)  ", kind:ErrorKind::Term, range:Range { start: 0, end: 5 }, chain:Some(Box::new(
            Error::unset_requirement(Input{src:"(test ?one)  ", input_pos:0, requirements:EnumSet::EMPTY}, Requirement::ObjectFluents.into())))
        };
        assert_eq!(term(Input::new("(test ?one)  ")), 
            Err(nom::Err::Error(test.clone())));
        // test.report("stdio").eprint(("stdio", Source::from("(test ?one)  ")));
        assert_eq!(term(Input::new("?hello")), 
            Ok((Input{src:"", input_pos:6, requirements:EnumSet::EMPTY}, Term::Variable((Range{start:0, end:6}, "hello")))));
        assert_eq!(typed_list(name, Input{src:"one two - object", input_pos:0, requirements:Requirement::Typing.into()}), 
            Ok((Input{src:"", input_pos:16, requirements:Requirement::Typing.into()}, 
            List{items:vec![(Range{start:0, end:3}, "one"), (Range{start:4, end:7}, "two")], kind:Type::Exact((Range{start:10, end:16}, "object"))})));
        assert_eq!(typed_list(name, Input::new("one two")), 
            Ok((Input{src:"", input_pos:7, requirements:EnumSet::EMPTY}, 
                List{items:vec![(Range{start:0, end:3}, "one"), (Range{start:4, end:7}, "two")], kind:Type::None})));
        assert_eq!(typed_list(variable, Input::new("?a1")), 
            Ok((Input{src:"", input_pos:3, requirements:EnumSet::EMPTY}, 
                List{items:vec![(Range{start:0, end:3}, "a1")], kind:Type::None})));
        assert_eq!(atomic_function_skeleton(Input::new("(testing ?left ?right)")), 
            Ok((Input{src:"", input_pos:22, requirements:EnumSet::EMPTY}, 
            AtomicFSkeleton{name:(Range{start:1, end:8}, "testing"), 
            variables:vec![List{items:vec![(Range{start:9, end:14}, "left"), (Range{start:15, end:21}, "right")], kind:Type::None}]})))
    }
    // #[test]
    // fn test_def() {
    //     assert_eq!(require_def("(:requirements :typing :strips)"), Ok(("", Requirement::Typing | Requirement::Strips)));
    //     assert_eq!(types_def("(:types one two three - object four five - three)", Requirement::Typing.into()), Ok(("", vec![List{items:vec!["one", "two", "three"], kind:Type::Exact("object")}, List{items:vec!["four", "five"], kind:Type::Exact("three")}])));
    //     assert_eq!(constants_def("(:constants one two three - object four five - three)", Requirement::Typing.into()), Ok(("", vec![List{items:vec!["one", "two", "three"], kind:Type::Exact("object")}, List{items:vec!["four", "five"], kind:Type::Exact("three")}])));
    //     assert_eq!(functions_def("(:functions (f1 ?a1) - 1)", Requirement::NumericFluents | Requirement::ObjectFluents), Ok(("", vec![FunctionTypedList{functions:vec![AtomicFSkeleton{name:"f1", variables:vec![List{items:vec!["a1"], kind:Type::None}]}], kind:FunctionType::Numeric(1)}])))
    // }

    // #[test]
    // fn test_print_error() {
    //     let src = "(test ?one)  ";
    //     if let Err(nom::Err::Error(e)) = term(src, EnumSet::EMPTY) {
    //         assert_eq!(e.report("report.pddl").print(("report.pddl", ariadne::Source::from(src))).is_ok(), true);
    //     }
    // }

}