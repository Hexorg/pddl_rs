pub mod ast;
pub mod input;

use crate::{Error, ErrorKind};

use self::{input::Input, ast::ConstraintGD};
use enumset::{EnumSet, enum_set};
use ast::Requirement::*;

use ast::*;

use nom::{self, 
    sequence::{pair, delimited, terminated, preceded, separated_pair, tuple}, 
    combinator::{recognize, map, opt, value}, 
    character::complete::{alpha1, multispace0, digit0, digit1}, 
    Parser, 
    InputTakeAtPosition, 
    branch::alt, 
    multi::{many0, fold_many1}, bytes::complete::is_not, InputLength};



type IResult<'src, O> = nom::IResult<Input<'src>, O, Error<'src>>;

fn err_name<'src>(ek: ErrorKind<'src>) -> impl FnMut(nom::Err<Error<'src>>) -> nom::Err<Error<'src>> {
    move |e| 
        e.map(|Error{input, chain, mut range, mut kind}| {
            let input = input.unwrap();
            use ErrorKind::*;
            let len = match ek {
                Nom(_) => todo!(),
                UnsetRequirement(_) => todo!(),
                Name |
                Variable |
                Term |
                FunctionType |
                GD |
                PreconditionExpression |
                FluentExpression |
                FunctionTypedList |
                Effect |
                Tag(_) => input.char_indices().find(|(_, c)| c.is_ascii_whitespace()).and_then(|(p, _)| Some(p)).unwrap_or(0),
                Many1(_) |
                UnclosedParenthesis|
                Parenthesis => 1,
                // Compiler errors:
                MissmatchedDomain(_) |
                ExpectedVariable |
                ExpectedName |
                UndeclaredVariable |
                UndefinedType => panic!(),
            };
            if let ErrorKind::Nom(_) = kind {
                range = range.start..(range.start+len);
                kind = ek;
            }
            Error{chain, input:Some(input), kind, range}
    })
}

pub fn check_requirements<'src, O, F>(mut parser:F, required:EnumSet<Requirement>, or:EnumSet<Requirement>) -> impl FnMut(Input<'src>) -> IResult<O> 
    where 
    O: 'src,
    F: Parser<Input<'src>, O, Error<'src>> {
        move |input: Input<'src>| {
            let (i, o) = parser.parse(input.clone())?;
            if !(i.requirements.is_superset(required) ||(!or.is_empty() && i.requirements.is_superset(or))) {
                Err(nom::Err::Failure(Error{
                    input:Some(input.src), 
                    kind: ErrorKind::UnsetRequirement(required), 
                    chain:None, 
                    range: input.input_pos..i.input_pos
                })) 
            } else {
                Ok((i, o))
            }
        }
}

pub fn alt_check_requirements<'src, O, F>(mut parser:F, required:EnumSet<Requirement>, or:EnumSet<Requirement>) -> impl FnMut(Input<'src>) -> IResult<O> 
    where 
    O: 'src,
    F: Parser<Input<'src>, O, Error<'src>> {
        move |input: Input<'src>| {
            let (i, o) = parser.parse(input.clone())?;
            if !(i.requirements.is_superset(required) ||(!or.is_empty() && i.requirements.is_superset(or))) {
                Err(nom::Err::Error(Error{
                    input:Some(input.src), 
                    kind: ErrorKind::UnsetRequirement(required), 
                    chain:None, 
                    range: input.input_pos..i.input_pos
                })) 
            } else {
                Ok((i, o))
            }
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

fn many1<'src, O, G>(mut parser:G, name:&'static str) -> impl FnMut(Input<'src>) -> IResult<Vec<O>> 
where 
    O:'src,
    G: FnMut(Input<'src>)->IResult<O> {
        move |i:Input<'src>| {
            let (i, o) = nom::multi::many1(|x|parser(x))(i).map_err(err_name(ErrorKind::Many1(name)))?;
            Ok((i, o))
        }
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
    move |i| nom::character::complete::char(c)(i).map(|(i, o)| {let end = i.input_pos; (i, (end-1..end, o))})
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

fn parens<'src, O2, G>(mut parser:G) -> impl FnMut(Input<'src>) -> IResult<O2> 
where 
    G: Parser<Input<'src>, O2, Error<'src>> {
    move |input| {
        let (i, _) = terminated(char('('), ignore)(input).map_err(err_name(ErrorKind::Parenthesis))?; 
        let (i, o) = parser.parse(i)?;
        let (i, _) = terminated(char(')'), ignore)(i).map_err(err_name(ErrorKind::UnclosedParenthesis))?;
        Ok((i, o))
    }
}

fn pddl_anyletter(input: Input) -> IResult<Input> {
    input.split_at_position_complete(|c| !(c.is_ascii_alphanumeric() || c == '_' || c == '-'))
}

// // ******************
// // ******************
// // ******************
// // ******************
// // ******************

/// Parse problem source code from a &str. Clossely follows Daniel L Kovacs' 
/// [spec](http://pddl4j.imag.fr/repository/wiki/BNF-PDDL-3.1.pdf)
/// ```

/// use pddl_rs::parser::{parse_domain, ast::Domain};
/// let domain = parse_domain("(define (domain test))");
/// assert_eq!(domain, Ok(
///     Domain{name:(16..20, "test"), 
///     requirements:enumset::EnumSet::EMPTY, 
///     types:vec![], 
///     constants:vec![],
///     predicates:vec![],
///     functions:vec![],
///     constraints:None,
///     actions:vec![]}))
/// ```
pub fn parse_domain<'src>(src:&'src str) -> Result<Domain<'src>, Error<'src>> {
    let input = Input{src, input_pos:0, requirements:EnumSet::EMPTY};
    match map(parens(tuple((
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
    })(input) {
        Ok((_, domain)) => Ok(domain),
        Err(nom::Err::Error(e)) | Err(nom::Err::Failure(e)) => Err(e),
        _ => panic!()
    }
}

fn require_def(input:Input) -> IResult<EnumSet<Requirement>> {
    parens(preceded(
        tag(":requirements"), 
        fold_many1(require_key, || EnumSet::EMPTY, |acc,kind| acc | kind)
    ))(input).map(|(mut i, o)| {i.requirements = o; (i, o)})
}

fn require_key(input:Input) -> IResult<Requirement> {
    alt((
        map(tag(":strips"), |_|Strips),
        map(tag(":typing"), |_|Typing),
        map(tag(":negative-preconditions"), |_|NegativePreconditions),
        map(tag(":disjunctive-preconditions"), |_|DisjunctivePreconditions),
        map(tag(":equality"), |_|Equality),
        map(tag(":existential-preconditions"), |_|ExistentialPreconditions),
        map(tag(":universal-preconditions"), |_|UniversalPreconditions),
        map(tag(":conditional-effects"), |_|ConditionalEffects),
        map(tag(":fluents"), |_|ObjectFluents),
        map(tag(":numeric-fluents"), |_|NumericFluents),
        map(tag(":durative-actions"), |_|DurativeActions),
        map(tag(":duration-inequalities"), |_|DurationInequalities),
        map(tag(":continuous-effects"), |_|ContinuousEffects),
        map(tag(":derived-predicates"), |_|DerivedPredicates),
        map(tag(":timed-initial-literals"), |_|TimedInitialLiterals),
        map(tag(":preferences"), |_|Preferences),
        map(tag(":constraints"), |_|Constraints),
        map(tag(":action-costs"), |_|ActionCosts),
    ))(input) 
}

fn types_def(input:Input) -> IResult<Vec<List>> {
    let r = input.requirements;
    let input_pos = input.input_pos;
    let result = parens(preceded(
        check_requirements(tag(":types"), enum_set!(Typing), enum_set!()), 
        typed_list(name)
    ))(input);
    input_pos;
    result
}

fn constants_def(input:Input) -> IResult<Vec<List>> {
    parens(preceded(
        tag(":constants"), 
        typed_list(name)
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
    parens(map(pair(
        function_symbol, 
        typed_list(variable)
    ),|(name, variables)| AtomicFSkeleton{name, variables}))(input)
}

use name as function_symbol;

fn functions_def(input:Input) -> IResult<Vec<FunctionTypedList>> {
    parens(preceded(
        check_requirements(tag(":functions"), enum_set!(ObjectFluents | NumericFluents), enum_set!(ActionCosts)), 
        many1(function_typed_list, "function typed list")
    ))(input)
}

fn function_typed_list(input:Input) -> IResult<FunctionTypedList> {
    alt((
        map(separated_pair(many1(atomic_function_skeleton, "atomic function skeleton"), minus_separated, function_type), |(functions, kind)| FunctionTypedList{functions, kind}),
        map(check_requirements(many1(atomic_function_skeleton, "atomic function skeleton"), enum_set!(NumericFluents), enum_set!()), |functions| FunctionTypedList{functions, kind:FunctionType::None})
        ))(input) //.map_err(err_name(ErrorKind::FunctionTypedList))
}

fn function_type(input:Input) -> IResult<FunctionType> {
    let src = input.src.chars().take(10).collect::<String>();
    alt((
        map(alt_check_requirements(digit0, enum_set!(NumericFluents), enum_set!()), |o:Input| FunctionType::Numeric((o.input_pos..(o.input_pos+o.input_len()), i64::from_str_radix(o.src, 10).unwrap()))),
        map(check_requirements(r#type, enum_set!(Typing | ObjectFluents), enum_set!(ActionCosts)), |t| FunctionType::Typed(t))
    ))(input).map_err(err_name(ErrorKind::FunctionType))
}

fn constraints(input:Input) -> IResult<ConstraintGD> {
    parens(preceded(
        check_requirements(tag(":constraints"), enum_set!(Constraints), enum_set!()), 
        con_gd
    ))(input)
}

fn structure_def(input:Input) -> IResult<Action> {
    alt((
        map(action_def, |a| Action::Basic(a)),
        map(durative_action_def, |a| Action::Durative(a)),
        // map(derived_def, |a| Action::Derived(a))
    ))(input)
}


fn typed_list<'src, G>(parser:G) -> impl FnMut(Input<'src>) -> IResult<Vec<List<'src>>>
where 
    G: FnMut(Input<'src>) -> IResult<Name<'src>>+Copy {
        move |input| alt((
            many1(map(separated_pair(many1(parser, "name or variable"), check_requirements(minus_separated, enum_set!(Typing), enum_set!()), r#type), |(items, kind)| List{items, kind}), "typed list"), 
            many1(map(many0(parser), |items| List{items, kind:Type::None}), "list"),
            map(many0(parser), |items| vec![List{items, kind:Type::None}])
        ))(input)
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
        preceded(tag(":parameters"), parens(typed_list(variable))),
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
                parens(typed_list(variable)),
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
                parens(typed_list(variable)),
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
    ))(input) //.map_err(err_name(ErrorKind::PreconditionExpression))
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
    ))(input) //.map_err(err_name(ErrorKind::Term))
}

fn function_term(input:Input) -> IResult<FunctionTerm> {
        check_requirements(parens(map(
            pair(function_symbol, many0(term)), 
            |(name, terms)| FunctionTerm{name, terms})),
            enum_set!(ObjectFluents), enum_set!(ActionCosts))(input)
}

fn f_exp(input:Input) -> IResult<Spanned<FluentExpression>> {
    alt((
        map(digit0, |o:Input| {let src = o.src; (o.into(), FluentExpression::Number(i64::from_str_radix(src, 10).unwrap()))}),
        map(parens(preceded(tag("-"), f_exp)), |(r, args)| (r.clone(), FluentExpression::Negate(Box::new((r, args))))),
        map(parens(preceded(tag("-"), pair(f_exp, f_exp))), |args| (args.0.0.start..args.1.0.end, FluentExpression::Subtract(Box::new(args)))),
        map(parens(preceded(tag("/"), pair(f_exp, f_exp))), |args| (args.0.0.start..args.1.0.end, FluentExpression::Divide(Box::new(args)))),
        map(parens(preceded(tag("+"), many1(f_exp, "fluent expression"))), |args| (args.range(), FluentExpression::Add(args))),
        map(parens(preceded(tag("*"), many1(f_exp, "fluent expression"))), |args| (args.range(), FluentExpression::Multiply(args))),
        map(f_head, |f| (f.range(), FluentExpression::Function(f)))
    ))(input) //.map_err(err_name(ErrorKind::FluentExpression))
}

fn f_head(input:Input) -> IResult<FunctionTerm> {
    alt((
        function_term,
        map(function_symbol, |name| FunctionTerm{name, terms:Vec::new()})
    ))(input)
}

fn name(input:Input) -> IResult<Name> {
    terminated(
        map(recognize(pair(alpha1, pddl_anyletter)), |o| (o.input_pos..(o.input_pos+o.src.len()), o.src)),
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
    ))(input) //.map_err(err_name(ErrorKind::Effect))
}

fn durative_action_def(input:Input) -> IResult<DurativeAction> {
    map(parens(tuple((
        tag(":durative-action"),
        da_symbol,
        tag(":parameters"),
        parens(typed_list(variable)),
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

/// Parse problem source code from a &str. Clossely follows Daniel L Kovacs' 
/// [spec](http://pddl4j.imag.fr/repository/wiki/BNF-PDDL-3.1.pdf)
/// ```
/// use pddl_rs::parser::{parse_problem, ast::{Problem, PreconditionExpr, GD, AtomicFormula, Term}};
/// let problem = parse_problem("(define (problem test) (:domain td) (:goal (end)))", enumset::EnumSet::EMPTY);
/// assert_eq!(problem, Ok(
///     Problem{name:(17..21, "test"), 
///     domain:(32..34, "td"),
///     requirements:enumset::EnumSet::EMPTY,
///     objects:vec![], 
///     init:vec![],
///     goal:PreconditionExpr::GD(GD::AtomicFormula(AtomicFormula::Predicate((44..47, "end"), vec![]))),
///     constraints:None,
///     metric:None}))
/// ```
pub fn parse_problem<'src>(src:&'src str, requirements:EnumSet<Requirement>) -> Result<Problem<'src>, Error<'src>> {
    let input = Input{src, input_pos:0, requirements};
    match map(parens(tuple((
        tag("define"),
        parens(pair(tag("problem"), name)),
        parens(pair(tag(":domain"), name)),
        opt(require_def),
        opt(parens(pair(tag(":objects"), typed_list(name)))),
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
    }})(input) {
        Ok((_, problem)) => Ok(problem),
        Err(nom::Err::Error(e)) | Err(nom::Err::Failure(e)) => Err(e),
        _ => panic!(),
    }
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
    use super::*;

    #[test]
    fn test_basic() {
        assert_eq!(pddl_anyletter(Input::new("H_ i")), 
            Ok((Input{src:" i", input_pos:2, requirements:EnumSet::EMPTY}, 
                Input::new("H_")
        )));
        assert_eq!(name(Input::new("He-l_lo world")), 
            Ok((Input{src:"world", input_pos:8, requirements:EnumSet::EMPTY}, 
            (0..7, "He-l_lo")
        )));
        assert_eq!(name(Input::new("#$Hello")), 
            Err(nom::Err::Error(Error{input:Some("#$Hello"), kind:ErrorKind::Name, chain:None, range:0..0}))
        );
        assert_eq!(variable(Input::new("?test me")), 
            Ok((Input{src:"me", input_pos:6, requirements:EnumSet::EMPTY}, (0..5,"test")
        )));

        assert_eq!(pair(name, variable)(Input::new("hello ?world")), 
            Ok((Input{src:"", input_pos:12, requirements:EnumSet::EMPTY}, ((0..5, "hello"), (6..12, "world")))));

        assert_eq!(term(Input{src:"(test ?one)  ", input_pos:0, requirements:enum_set!(ObjectFluents)}), 
            Ok((Input{src:"", input_pos:13, requirements:enum_set!(ObjectFluents)}, 
            Term::Function(FunctionTerm{name:(1..5, "test"), terms:vec![Term::Variable((6..10, "one"))]})
        )));
        let test = Error { input: Some("(test ?one)  "), kind:ErrorKind::UnsetRequirement(enum_set!(ObjectFluents)), chain: None, range: 0..13 };
        // test.clone().report("stdio").eprint(("stdio", ariadne::Source::from("(test ?one)  ")));
        assert_eq!(term(Input::new("(test ?one)  ")), 
            Err(nom::Err::Failure(test)));
        assert_eq!(term(Input::new("?hello")), 
            Ok((Input{src:"", input_pos:6, requirements:EnumSet::EMPTY}, Term::Variable((0..6, "hello")))));
        assert_eq!(typed_list(name)(Input{src:"one two - object", input_pos:0, requirements:enum_set!(Typing)}), 
            Ok((Input{src:"", input_pos:16, requirements:enum_set!(Typing)}, 
            vec![List{items:vec![(0..3, "one"), (4..7, "two")], kind:Type::Exact((10..16, "object"))}])));
        assert_eq!(typed_list(name)(Input::new("one two")), 
            Ok((Input{src:"", input_pos:7, requirements:EnumSet::EMPTY}, 
                vec![List{items:vec![(0..3, "one"), (4..7, "two")], kind:Type::None}])));
        assert_eq!(typed_list(variable)(Input::new("?a1")), 
            Ok((Input{src:"", input_pos:3, requirements:EnumSet::EMPTY}, 
                vec![List{items:vec![(0..3, "a1")], kind:Type::None}])));
        assert_eq!(atomic_function_skeleton(Input::new("(testing ?left ?right)")), 
            Ok((Input{src:"", input_pos:22, requirements:EnumSet::EMPTY}, 
            AtomicFSkeleton{name:(1..8, "testing"), 
            variables:vec![List{items:vec![(9..14, "left"), (15..21, "right")], kind:Type::None}]})))
    }

    #[test]
    fn test_typed_list() {
        assert_eq!(typed_list(variable)(Input::new("?one ?two")), Ok((Input{src:"", input_pos:9, requirements:EnumSet::EMPTY}, vec![List{items:vec![(0..4, "one"), (5..9, "two")], kind:Type::None}])));
    }
    // #[test]
    // fn test_def() {
    //     assert_eq!(require_def("(:requirements :typing :strips)"), Ok(("", Typing | Strips)));
    //     assert_eq!(types_def("(:types one two three - object four five - three)", enum_set!(Typing)), Ok(("", vec![List{items:vec!["one", "two", "three"], kind:Type::Exact("object")}, List{items:vec!["four", "five"], kind:Type::Exact("three")}])));
    //     assert_eq!(constants_def("(:constants one two three - object four five - three)", enum_set!(Typing)), Ok(("", vec![List{items:vec!["one", "two", "three"], kind:Type::Exact("object")}, List{items:vec!["four", "five"], kind:Type::Exact("three")}])));
    //     assert_eq!(functions_def("(:functions (f1 ?a1) - 1)", NumericFluents | ObjectFluents), Ok(("", vec![FunctionTypedList{functions:vec![AtomicFSkeleton{name:"f1", variables:vec![List{items:vec!["a1"], kind:Type::None}]}], kind:FunctionType::Numeric(1)}])))
    // }

    // #[test]
    // fn test_print_error() {
    //     let src = "(test ?one)  ";
    //     if let Err(nom::Err::Error(e)) = term(src, EnumSet::EMPTY) {
    //         assert_eq!(e.report("report.pddl").print(("report.pddl", ariadne::Source::from(src))).is_ok(), true);
    //     }
    // }

}