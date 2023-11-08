pub mod ast;
mod input;

use crate::{Error, ErrorKind};

use ast::Requirement::*;
use enumset::{enum_set, EnumSet};

use ast::*;

pub use input::Input;

use nom::{
    self,
    branch::alt,
    bytes::complete::is_not,
    character::complete::{alpha1, digit0, digit1, multispace0},
    combinator::{cut, map, opt, recognize, value},
    multi::{fold_many1, many0},
    sequence::{delimited, pair, preceded, separated_pair, terminated, tuple},
    InputTakeAtPosition, Parser,
};

type IResult<'src, O> = nom::IResult<Input<'src>, O, Error>;

#[inline]
fn err_name<'src>(ek: ErrorKind) -> impl FnMut(nom::Err<Error>) -> nom::Err<Error> {
    move |e| {
        e.map(|mut old_e| {
            // use ErrorKind::*;
            old_e.kind = ek;
            old_e
        })
    }
}

#[inline]
fn check_requirements<'src, O, F>(
    mut parser: F,
    required: EnumSet<Requirement>,
    or: EnumSet<Requirement>,
) -> impl FnMut(Input<'src>) -> IResult<O>
where
    O: 'src,
    F: Parser<Input<'src>, O, Error>,
{
    move |input: Input<'src>| {
        let (i, o) = parser.parse(input.clone())?;
        if !(i.requirements.is_superset(required)
            || (!or.is_empty() && i.requirements.is_superset(or)))
        {
            Err(nom::Err::Failure(Error {
                // input: Some(input.src),
                kind: ErrorKind::UnsetRequirement(required),
                chain: None,
                span: input.span_end(i.input_pos),
            }))
        } else {
            Ok((i, o))
        }
    }
}

#[inline]
fn alt_check_requirements<'src, O, F>(
    mut parser: F,
    required: EnumSet<Requirement>,
    or: EnumSet<Requirement>,
) -> impl FnMut(Input<'src>) -> IResult<O>
where
    O: 'src,
    F: Parser<Input<'src>, O, Error>,
{
    move |input: Input<'src>| {
        if !(input.requirements.is_superset(required)
            || (!or.is_empty() && input.requirements.is_superset(or)))
        {
            let span = match parser.parse(input.clone()) {
                Ok((i, _)) => input.span_end(i.input_pos),
                Err(nom::Err::Error(e)) | Err(nom::Err::Failure(e)) => e.span,
                _ => input.into(),
            };
            Err(err_name(ErrorKind::UnsetRequirement(required))(
                nom::Err::Error(Error {
                    // input: Some(input.src),
                    kind: ErrorKind::UnsetRequirement(required),
                    chain: None,
                    span,
                }),
            ))
        } else {
            parser.parse(input)
        }
    }
}

#[inline]
fn ignore<'src>(input: Input<'src>) -> IResult<()> {
    value(
        (),
        multispace0
            .and(opt(pair(char(';'), is_not("\n"))))
            .and(multispace0),
    )(input)
}

#[inline]
fn tag<'src>(tag_name: &'static str) -> impl Parser<Input<'src>, (), Error> {
    value(
        (),
        terminated(
            move |i| {
                nom::bytes::complete::tag(tag_name)(i).map_err(err_name(ErrorKind::Tag(tag_name)))
            },
            ignore,
        ),
    )
}

#[inline]
fn many1<'src, O, G>(
    mut parser: G,
    name: &'static str,
) -> impl FnMut(Input<'src>) -> IResult<Vec<O>>
where
    O: 'src,
    G: FnMut(Input<'src>) -> IResult<O>,
{
    move |i: Input<'src>| {
        let (i, o) =
            nom::multi::many1(|x| parser(x))(i).map_err(err_name(ErrorKind::Many1(name)))?;
        Ok((i, o))
    }
}

#[inline]
fn minus_separated(input: Input) -> IResult<Spanned<char>> {
    delimited(multispace0, char('-'), multispace0)(input)
}

#[inline]
fn preceded_span_included<'src, O1, O2, F, G>(
    mut first: F,
    mut second: G,
) -> impl FnMut(Input<'src>) -> IResult<O2>
where
    O1: SpannedAst<'src> + 'src,
    O2: SpannedAstMut<'src> + 'src,
    F: Parser<Input<'src>, O1, Error>,
    G: Parser<Input<'src>, O2, Error>,
{
    move |input: Input<'src>| {
        let origin = input.input_pos;
        let (input, _) = first.parse(input)?;
        let (input, mut o2) = second.parse(input)?;
        o2.span_mut().start = origin;
        Ok((input, o2))
    }
}

#[inline]
fn char(c: char) -> impl Fn(Input) -> IResult<Spanned<char>> {
    move |input| {
        nom::character::complete::char(c)(input).map(|(i, o)| (i, (input.span_end(i.input_pos), o)))
    }
}

#[inline]
fn parens<'src, O2, G>(mut parser: G) -> impl FnMut(Input<'src>) -> IResult<O2>
where
    G: Parser<Input<'src>, O2, Error>,
{
    move |input| {
        let open_paren_pos = input.input_pos;
        let (i, _) =
            terminated(char('('), ignore)(input).map_err(err_name(ErrorKind::Parenthesis))?;
        let (i, o) = parser.parse(i)?;
        let (i, _) = terminated(cut(char(')')), ignore)(i)
            .map_err(err_name(ErrorKind::UnclosedParenthesis(open_paren_pos)))?;
        Ok((i, o))
    }
}

#[inline]
fn parens_alt<'src, O2, G>(mut parser: G) -> impl FnMut(Input<'src>) -> IResult<O2>
where
    G: Parser<Input<'src>, O2, Error>,
{
    move |input| {
        let open_paren_pos = input.input_pos;
        let (i, _) =
            terminated(char('('), ignore)(input).map_err(err_name(ErrorKind::Parenthesis))?;
        let (i, o) = parser.parse(i)?;
        let (i, _) = terminated(char(')'), ignore)(i)
            .map_err(err_name(ErrorKind::UnclosedParenthesis(open_paren_pos)))?;
        Ok((i, o))
    }
}

#[inline]
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

/// use pddl_rs::parser::{parse_domain, ast::{Name, Domain}};
/// let domain = parse_domain("(define (domain test))");
/// assert_eq!(domain, Ok(
///     Domain{name:Name::new(16..20, "test"),
///     requirements:enumset::EnumSet::EMPTY,
///     types:vec![],
///     constants:vec![],
///     predicates:vec![],
///     functions:vec![],
///     constraints:None,
///     actions:vec![]}))
/// ```
pub fn parse_domain<'src>(src: &'src str) -> Result<Domain<'src>, Error> {
    let input = Input {
        // filename,
        src,
        is_problem: false,
        input_pos: 0,
        requirements: EnumSet::EMPTY,
    };
    match map(
        parens(tuple((
            tag("define"),
            parens(pair(tag("domain"), name)),
            opt(require_def),
            opt(types_def),
            opt(constants_def),
            opt(predicates_def),
            opt(functions_def),
            opt(constraints),
            many0(structure_def),
        ))),
        |(
            (),
            ((), name),
            requirements,
            types,
            constants,
            predicates,
            functions,
            constraints,
            actions,
        )| Domain {
            name,
            requirements: requirements.unwrap_or_default(),
            types: types.unwrap_or_default(),
            constants: constants.unwrap_or_default(),
            predicates: predicates.unwrap_or_default(),
            functions: functions.unwrap_or_default(),
            constraints,
            actions,
        },
    )(input)
    {
        Ok((_, domain)) => Ok(domain),
        Err(nom::Err::Error(e)) | Err(nom::Err::Failure(e)) => Err(e),
        _ => panic!(),
    }
}

#[inline]
fn require_def(input: Input) -> IResult<EnumSet<Requirement>> {
    parens(preceded(
        tag(":requirements"),
        cut(fold_many1(
            require_key,
            || EnumSet::EMPTY,
            |acc, kind| acc | kind,
        )),
    ))(input)
    .map(|(mut i, o)| {
        i.requirements = o;
        (i, o)
    })
}

#[inline]
fn require_key(input: Input) -> IResult<Requirement> {
    alt((
        map(tag(":strips"), |_| Strips),
        map(tag(":typing"), |_| Typing),
        map(tag(":negative-preconditions"), |_| NegativePreconditions),
        map(tag(":disjunctive-preconditions"), |_| {
            DisjunctivePreconditions
        }),
        map(tag(":equality"), |_| Equality),
        map(tag(":existential-preconditions"), |_| {
            ExistentialPreconditions
        }),
        map(tag(":universal-preconditions"), |_| UniversalPreconditions),
        map(tag(":conditional-effects"), |_| ConditionalEffects),
        map(tag(":fluents"), |_| ObjectFluents),
        map(tag(":numeric-fluents"), |_| NumericFluents),
        map(tag(":durative-actions"), |_| DurativeActions),
        map(tag(":duration-inequalities"), |_| DurationInequalities),
        map(tag(":continuous-effects"), |_| ContinuousEffects),
        map(tag(":derived-predicates"), |_| DerivedPredicates),
        map(tag(":timed-initial-literals"), |_| TimedInitialLiterals),
        map(tag(":preferences"), |_| Preferences),
        map(tag(":constraints"), |_| Constraints),
        map(tag(":action-costs"), |_| ActionCosts),
    ))(input)
}

#[inline]
fn types_def(input: Input) -> IResult<Vec<List>> {
    parens(preceded(
        check_requirements(tag(":types"), enum_set!(Typing), enum_set!()),
        cut(typed_list(name)),
    ))(input)
}

#[inline]
fn constants_def(input: Input) -> IResult<Vec<List>> {
    parens(preceded(tag(":constants"), cut(typed_list(name))))(input)
}

#[inline]
fn predicates_def(input: Input) -> IResult<Vec<AtomicFSkeleton>> {
    parens(preceded(
        tag(":predicates"),
        cut(many1(atomic_function_skeleton, "atomic function skeleton")),
    ))(input)
}

use name as predicate;

#[inline]
fn variable(input: Input) -> IResult<Name> {
    preceded_span_included(char('?'), name)(input).map_err(err_name(ErrorKind::Variable))
}

#[inline]
fn atomic_function_skeleton(input: Input) -> IResult<AtomicFSkeleton> {
    parens(map(
        pair(function_symbol, typed_list(variable)),
        |(name, variables)| AtomicFSkeleton { name, variables },
    ))(input)
}

use name as function_symbol;

#[inline]
fn functions_def(input: Input) -> IResult<Vec<FunctionTypedList>> {
    parens(preceded(
        check_requirements(
            tag(":functions"),
            enum_set!(ObjectFluents | NumericFluents),
            enum_set!(ActionCosts),
        ),
        cut(many1(function_typed_list, "function typed list")),
    ))(input)
}

#[inline]
fn function_typed_list(input: Input) -> IResult<FunctionTypedList> {
    alt((
        map(
            separated_pair(
                many1(atomic_function_skeleton, "atomic function skeleton"),
                minus_separated,
                function_type,
            ),
            |(functions, kind)| FunctionTypedList { functions, kind },
        ),
        map(
            check_requirements(
                many1(atomic_function_skeleton, "atomic function skeleton"),
                enum_set!(NumericFluents),
                enum_set!(),
            ),
            |functions| FunctionTypedList {
                functions,
                kind: FunctionType::None,
            },
        ),
    ))(input)
    .map_err(err_name(ErrorKind::FunctionTypedList))
}

#[inline]
fn function_type(input: Input) -> IResult<FunctionType> {
    alt((
        map(
            alt_check_requirements(digit0, enum_set!(NumericFluents), enum_set!()),
            |o: Input| FunctionType::Numeric((o.into(), i64::from_str_radix(o.src, 10).unwrap())),
        ),
        map(
            check_requirements(
                r#type,
                enum_set!(Typing | ObjectFluents),
                enum_set!(ActionCosts),
            ),
            |t| FunctionType::Typed(t),
        ),
    ))(input)
    .map_err(err_name(ErrorKind::FunctionType))
}

#[inline]
fn constraints(input: Input) -> IResult<ConstraintGD> {
    parens(preceded(
        check_requirements(tag(":constraints"), enum_set!(Constraints), enum_set!()),
        cut(con_gd),
    ))(input)
}

#[inline]
fn structure_def(input: Input) -> IResult<Action> {
    alt((
        map(action_def, |a| Action::Basic(a)),
        map(durative_action_def, |a| Action::Durative(a)),
        // map(derived_def, |a| Action::Derived(a))
    ))(input)
    .map_err(err_name(ErrorKind::StructureDef))
}

#[inline]
fn typed_list<'src, G>(parser: G) -> impl FnMut(Input<'src>) -> IResult<Vec<List<'src>>>
where
    G: FnMut(Input<'src>) -> IResult<Name<'src>> + Copy,
{
    move |input| {
        alt((
            many1(
                map(
                    separated_pair(
                        many1(parser, "name or variable"),
                        check_requirements(minus_separated, enum_set!(Typing), enum_set!()),
                        r#type,
                    ),
                    |(items, kind)| List { items, kind },
                ),
                "typed list",
            ),
            many1(
                map(many0(parser), |items| List {
                    items,
                    kind: Type::None,
                }),
                "list",
            ),
            map(many0(parser), |items| {
                vec![List {
                    items,
                    kind: Type::None,
                }]
            }),
        ))(input)
        .map_err(err_name(ErrorKind::TypedList))
    }
}

use name as primitive_type;

#[inline]
fn r#type(input: Input) -> IResult<Type> {
    alt((
        map(primitive_type, |o| Type::Exact(o)),
        map(
            preceded(
                delimited(multispace0, tag("either"), multispace0),
                cut(many1(primitive_type, "primitive type")),
            ),
            |vec| Type::Either(vec),
        ),
    ))(input)
    .map_err(err_name(ErrorKind::Type))
}

#[inline]
fn empty_or<'src, O2, G>(parser: G) -> impl FnMut(Input<'src>) -> IResult<Option<O2>>
where
    O2: 'src,
    G: FnMut(Input<'src>) -> IResult<O2> + Copy,
{
    alt((map(tag("()"), |_| None), map(parser, |p| Some(p))))
}

#[inline]
fn action_def(input: Input) -> IResult<BasicAction> {
    map(
        parens(tuple((
            preceded(tag(":action"), cut(action_symbol)),
            preceded(tag(":parameters"), cut(parens(typed_list(variable)))),
            map(
                opt(preceded(tag(":precondition"), cut(empty_or(pre_gd)))),
                |o| o.and_then(|f| f),
            ),
            map(opt(preceded(tag(":effect"), cut(empty_or(effect)))), |o| {
                o.and_then(|f| f)
            }),
        ))),
        |(name, parameters, precondition, effect)| BasicAction {
            name,
            parameters,
            precondition,
            effect,
        },
    )(input)
}

#[inline]
fn forall<'src, O2, G>(parser: G) -> impl FnMut(Input<'src>) -> IResult<Forall<O2>>
where
    O2: 'src,
    G: FnMut(Input<'src>) -> IResult<O2> + Copy,
{
    parens(preceded(
        tag("forall"),
        cut(map(
            pair(parens(typed_list(variable)), parser),
            |(variables, gd)| Forall {
                variables,
                gd: Box::new(gd),
            },
        )),
    ))
}

#[inline]
fn exists<'src, O2, G>(parser: G) -> impl FnMut(Input<'src>) -> IResult<Exists<O2>>
where
    O2: 'src,
    G: FnMut(Input<'src>) -> IResult<O2> + Copy,
{
    parens(preceded(
        tag("exists"),
        cut(map(
            pair(parens(typed_list(variable)), parser),
            |(variables, gd)| Forall {
                variables,
                gd: Box::new(gd),
            },
        )),
    ))
}

#[inline]
fn preference<'src, O2, G>(parser: G) -> impl FnMut(Input<'src>) -> IResult<Preference<O2>>
where
    O2: 'src,
    G: FnMut(Input<'src>) -> IResult<O2>,
{
    parens(preceded(
        tag("preference"),
        cut(map(pair(opt(pref_name), parser), |(name, gd)| Preference {
            name,
            gd,
        })),
    ))
}

#[inline]
fn pre_gd(input: Input) -> IResult<PreconditionExpr> {
    alt((
        map(parens(preceded(tag("and"), cut(many0(pre_gd)))), |vec| {
            PreconditionExpr::And(vec)
        }),
        map(forall(pre_gd), |forall| PreconditionExpr::Forall(forall)),
        map(preference(gd), |pref| PreconditionExpr::Preference(pref)),
        map(gd, |gd| PreconditionExpr::GD(gd)),
    ))(input)
    .map_err(err_name(ErrorKind::PreconditionExpression))
}

use name as pref_name;

#[inline]
fn gd(input: Input) -> IResult<GD> {
    alt((
        map(atomic_formula(term), |af| GD::AtomicFormula(af)),
        map(literal(term), |lit| match lit {
            NegativeFormula::Direct(af) => GD::AtomicFormula(af),
            NegativeFormula::Not(af) => GD::Not(Box::new(GD::AtomicFormula(af))),
        }),
        map(parens(preceded(tag("and"), many0(gd))), |gd| GD::And(gd)),
        map(parens(preceded(tag("or"), many0(gd))), |gd| GD::Or(gd)),
        map(parens(preceded(tag("not"), gd)), |gd| GD::Not(Box::new(gd))),
        map(parens(preceded(tag("imply"), pair(gd, gd))), |t| {
            GD::Imply(Box::new(t))
        }),
        map(exists(gd), |e| GD::Exists(e)),
        map(forall(gd), |f| GD::Forall(f)),
    ))(input)
    .map_err(err_name(ErrorKind::GD))
}
use name as action_symbol;

#[inline]
fn literal<'src, O2, G>(parser: G) -> impl FnMut(Input<'src>) -> IResult<NegativeFormula<O2>>
where
    O2: 'src,
    G: Copy + FnMut(Input<'src>) -> IResult<O2>,
{
    move |i| {
        alt((
            map(
                parens(preceded(tag("not"), cut(atomic_formula(parser)))),
                |af| NegativeFormula::Not(af),
            ),
            map(atomic_formula(parser), |af| NegativeFormula::Direct(af)),
        ))(i)
        .map_err(err_name(ErrorKind::Literal))
    }
}

#[inline]
fn atomic_formula<'src, O2, G>(parser: G) -> impl FnMut(Input<'src>) -> IResult<AtomicFormula<O2>>
where
    O2: 'src,
    G: FnMut(Input<'src>) -> IResult<O2> + Copy,
{
    move |i| {
        alt((
            map(
                parens_alt(pair(predicate, many0(parser))),
                |(predicate, vec)| AtomicFormula::Predicate(predicate, vec),
            ),
            map(
                parens(preceded(tag("="), pair(parser, parser))),
                |(left, right)| AtomicFormula::Equality(left, right),
            ),
        ))(i)
        .map_err(err_name(ErrorKind::AtomicFormula))
    }
}

#[inline]
fn term(input: Input) -> IResult<Term> {
    alt((
        map(variable, |o| Term::Variable(o)),
        map(name, |o| Term::Name(o)),
        alt_check_requirements(
            map(function_term, |o| Term::Function(o)),
            enum_set!(ObjectFluents),
            enum_set!(ActionCosts),
        ),
    ))(input)
    .map_err(err_name(ErrorKind::Term))
}

#[inline]
fn function_term(input: Input) -> IResult<FunctionTerm> {
    check_requirements(
        parens_alt(map(pair(function_symbol, many0(term)), |(name, terms)| {
            FunctionTerm { name, terms }
        })),
        enum_set!(ObjectFluents),
        enum_set!(ActionCosts),
    )(input)
    .map_err(err_name(ErrorKind::FunctionTerm))
}

#[inline]
fn f_exp(input: Input) -> IResult<Spanned<FluentExpression>> {
    alt((
        map(digit0, |o: Input| {
            let src = o.src;
            (
                o.into(),
                FluentExpression::Number(i64::from_str_radix(src, 10).unwrap()),
            )
        }),
        map(parens(preceded(tag("-"), cut(f_exp))), |(r, args)| {
            (r.clone(), FluentExpression::Negate(Box::new((r, args))))
        }),
        map(
            parens(preceded(tag("-"), cut(pair(f_exp, f_exp)))),
            |args| {
                (
                    args.0 .0.change_end(args.1 .0.end),
                    FluentExpression::Subtract(Box::new(args)),
                )
            },
        ),
        map(
            parens(preceded(tag("/"), cut(pair(f_exp, f_exp)))),
            |args| {
                (
                    args.0 .0.change_end(args.1 .0.end),
                    FluentExpression::Divide(Box::new(args)),
                )
            },
        ),
        map(
            parens(preceded(tag("+"), cut(many1(f_exp, "fluent expression")))),
            |args| (args.span(), FluentExpression::Add(args)),
        ),
        map(
            parens(preceded(tag("*"), cut(many1(f_exp, "fluent expression")))),
            |args| (args.span(), FluentExpression::Multiply(args)),
        ),
        map(f_head, |f| (f.span(), FluentExpression::Function(f))),
    ))(input)
    .map_err(err_name(ErrorKind::FluentExpression))
}

#[inline]
fn f_head(input: Input) -> IResult<FunctionTerm> {
    alt((
        function_term,
        map(function_symbol, |name| FunctionTerm {
            name,
            terms: Vec::new(),
        }),
    ))(input)
}

#[inline]
fn name(input: Input) -> IResult<Name> {
    terminated(
        map(recognize(pair(alpha1, pddl_anyletter)), |o| {
            let span = Span {
                start: input.input_pos,
                end: input.input_pos + o.src.len(),
                is_problem: input.is_problem,
            };
            Name(span, o.src)
        }),
        ignore,
    )(input)
    .map_err(err_name(ErrorKind::Name))
}

#[inline]
fn effect(input: Input) -> IResult<Effect> {
    alt((
        map(parens(preceded(tag("and"), cut(many0(effect)))), |vec| {
            Effect::And(vec)
        }),
        map(forall(effect), |forall| Effect::Forall(forall)),
        map(
            parens(preceded(tag("when"), cut(pair(gd, effect)))),
            |(gd, effect)| {
                Effect::When(When {
                    gd,
                    effect: Box::new(effect),
                })
            },
        ),
        map(literal(term), |l| Effect::NegativeFormula(l)),
        map(
            parens(preceded(tag("scale-up"), cut(pair(f_head, f_exp)))),
            |(t, e)| Effect::ScaleUp(t, e),
        ),
        map(
            parens(preceded(tag("scale-down"), cut(pair(f_head, f_exp)))),
            |(t, e)| Effect::ScaleDown(t, e),
        ),
        map(
            parens(preceded(tag("increase"), cut(pair(f_head, f_exp)))),
            |(t, e)| Effect::Increase(t, e),
        ),
        map(
            parens(preceded(tag("decrease"), cut(pair(f_head, f_exp)))),
            |(t, e)| Effect::Decrease(t, e),
        ),
        map(
            parens(preceded(tag("assign"), pair(f_head, f_exp))),
            |(t, e)| Effect::Assign(t, e),
        ),
        map(
            parens(preceded(tag("assign"), pair(function_term, term))),
            |(t, e)| Effect::AssignTerm(t, e),
        ),
        map(
            parens(preceded(tag("assign"), pair(f_head, tag("undefined")))),
            |(t, _)| Effect::AssignUndefined(t),
        ),
    ))(input)
    .map_err(err_name(ErrorKind::Effect))
}

#[inline]
fn durative_action_def(input: Input) -> IResult<DurativeAction> {
    map(
        parens(tuple((
            tag(":durative-action"),
            cut(da_symbol),
            tag(":parameters"),
            cut(parens(typed_list(variable))),
            tag(":duration"),
            cut(duration_contraint),
            tag(":condition"),
            cut(empty_or(da_gd)),
            tag(":effect"),
            cut(empty_or(da_effect)),
        ))),
        |((), name, (), parameters, (), duration, (), condition, (), effect)| DurativeAction {
            name,
            parameters,
            duration,
            condition,
            effect,
        },
    )(input)
}

use name as da_symbol;

#[inline]
fn da_gd(input: Input) -> IResult<DurationGD> {
    alt((
        map(timed_gd, |tgd| DurationGD::GD(tgd)),
        map(preference(timed_gd), |pref| DurationGD::Preference(pref)),
        map(parens(preceded(tag("and"), cut(many0(da_gd)))), |vec| {
            DurationGD::And(vec)
        }),
        map(forall(da_gd), |forall| DurationGD::Forall(forall)),
    ))(input)
}

#[inline]
fn timed_gd(input: Input) -> IResult<TimedGD> {
    parens(alt((
        map(pair(tag("at start"), cut(gd)), |((), gd)| {
            TimedGD::AtStart(gd)
        }),
        map(pair(tag("at end"), cut(gd)), |((), gd)| TimedGD::AtEnd(gd)),
        map(pair(tag("over all"), cut(gd)), |((), gd)| {
            TimedGD::OverAll(gd)
        }),
    )))(input)
}

#[inline]
fn duration_contraint(input: Input) -> IResult<DurationConstraint> {
    parens(alt((
        map(
            pair(tag("and"), cut(many0(duration_contraint))),
            |((), vec)| DurationConstraint::And(vec),
        ),
        map(tag("()"), |_| DurationConstraint::None),
        map(pair(tag("<= ?duration"), cut(f_exp)), |((), exp)| {
            DurationConstraint::LessThanOrEquals(exp)
        }),
        map(pair(tag(">= ?duration"), cut(f_exp)), |((), exp)| {
            DurationConstraint::GreaterOrEquals(exp)
        }),
        map(pair(tag("= ?duration"), cut(f_exp)), |((), exp)| {
            DurationConstraint::Equals(exp)
        }),
        map(pair(tag("at start"), cut(duration_contraint)), |((), d)| {
            DurationConstraint::AtStart(Box::new(d))
        }),
        map(pair(tag("at end"), cut(duration_contraint)), |((), d)| {
            DurationConstraint::AtEnd(Box::new(d))
        }),
    )))(input)
}

#[inline]
fn da_effect(input: Input) -> IResult<DurationEffect> {
    parens(alt((
        map(pair(tag("and"), cut(many0(da_effect))), |((), vec)| {
            DurationEffect::And(vec)
        }),
        map(timed_effect, |gd| DurationEffect::GD(gd)),
        map(forall(da_effect), |forall| DurationEffect::Forall(forall)),
        map(
            parens(preceded(tag("when"), cut(pair(da_gd, timed_effect)))),
            |(gd, effect)| {
                DurationEffect::When(When {
                    gd,
                    effect: Box::new(effect),
                })
            },
        ),
    )))(input)
}

#[inline]
fn timed_effect(input: Input) -> IResult<TimedEffect> {
    alt((
        map(pair(tag("at start"), cut(effect)), |((), e)| {
            TimedEffect::AtStart(e)
        }),
        map(pair(tag("at end"), cut(effect)), |((), e)| {
            TimedEffect::AtEnd(e)
        }),
        map(effect, |e| TimedEffect::Effect(e)),
    ))(input)
}

/// Parse problem source code from a &str. Clossely follows Daniel L Kovacs'
/// [spec](http://pddl4j.imag.fr/repository/wiki/BNF-PDDL-3.1.pdf)
/// ```
/// use pddl_rs::parser::{parse_problem, ast::{Name, Problem, PreconditionExpr, GD, AtomicFormula, Term}};
/// let problem = parse_problem("(define (problem test) (:domain td) (:goal (end)))", enumset::EnumSet::EMPTY);
/// assert_eq!(problem, Ok(
///     Problem{name:Name::new(17..21, "test"),
///     domain:Name::new(32..34, "td"),
///     requirements:enumset::EnumSet::EMPTY,
///     objects:vec![],
///     init:vec![],
///     goal:PreconditionExpr::GD(GD::AtomicFormula(AtomicFormula::Predicate(Name::new(44..47, "end"), vec![]))),
///     constraints:None,
///     metric:None}))
/// ```
pub fn parse_problem<'src>(
    src: &'src str,
    requirements: EnumSet<Requirement>,
) -> Result<Problem<'src>, Error> {
    let input = Input {
        is_problem: true,
        src,
        input_pos: 0,
        requirements,
    };
    match map(
        parens(tuple((
            tag("define"),
            parens(pair(tag("problem"), name)),
            parens(pair(tag(":domain"), name)),
            opt(require_def),
            opt(parens(pair(tag(":objects"), cut(typed_list(name))))),
            opt(parens(pair(tag(":init"), cut(many0(init_el))))),
            parens(pair(tag(":goal"), pre_gd)),
            opt(parens(pair(tag(":constraints"), cut(pref_con_gd)))),
            opt(parens(pair(tag(":metric"), cut(metric_spec)))),
        ))),
        |(
            (),
            ((), name),
            ((), domain),
            requirements,
            objects,
            init,
            ((), goal),
            constraints,
            metric,
        )| {
            let requirements = requirements.unwrap_or(EnumSet::EMPTY);
            let objects = objects.and_then(|((), o)| Some(o)).unwrap_or_default();
            let init = init.and_then(|((), o)| Some(o)).unwrap_or_default();
            let constraints = constraints.and_then(|((), o)| Some(o));
            let metric = metric.and_then(|((), o)| Some(o));
            Problem {
                name,
                domain,
                requirements,
                objects,
                init,
                goal,
                constraints,
                metric,
            }
        },
    )(input)
    {
        Ok((_, problem)) => Ok(problem),
        Err(nom::Err::Error(e)) | Err(nom::Err::Failure(e)) => Err(e),
        _ => panic!(),
    }
}

#[inline]
fn init_el(input: Input) -> IResult<Init> {
    alt((
        map(literal(name), |l| Init::AtomicFormula(l)),
        map(
            parens(tuple((tag("at"), cut(digit1), cut(literal(name))))),
            |((), Input { src, .. }, literal)| {
                Init::At(i64::from_str_radix(src, 10).unwrap(), literal)
            },
        ),
        map(
            parens(tuple((tag("="), cut(function_term), cut(digit1)))),
            |((), term, Input { src, .. })| {
                Init::Equals(term, i64::from_str_radix(src, 10).unwrap())
            },
        ),
        map(
            parens(tuple((tag("="), cut(function_term), cut(name)))),
            |((), term, name)| Init::Is(term, name),
        ),
    ))(input)
}

#[inline]
fn pref_con_gd(input: Input) -> IResult<PrefConstraintGD> {
    alt((
        map(
            parens(pair(tag("and"), cut(many0(pref_con_gd)))),
            |((), vec)| PrefConstraintGD::And(vec),
        ),
        map(forall(pref_con_gd), |forall| {
            PrefConstraintGD::Forall(forall)
        }),
        map(preference(con_gd), |pref| {
            PrefConstraintGD::Preference(pref)
        }),
        map(con_gd, |gd| PrefConstraintGD::GD(gd)),
    ))(input)
}

#[inline]
fn con_gd(input: Input) -> IResult<ConstraintGD> {
    alt((
        map(parens(preceded(tag("and"), cut(many0(con_gd)))), |f| {
            ConstraintGD::And(f)
        }),
        map(forall(con_gd), |forall| ConstraintGD::Forall(forall)),
        map(pair(tag("at end"), cut(gd)), |((), gd)| {
            ConstraintGD::AtEnd(gd)
        }),
        map(pair(tag("always"), cut(gd)), |((), gd)| {
            ConstraintGD::Always(gd)
        }),
        map(pair(tag("sometime"), cut(gd)), |((), gd)| {
            ConstraintGD::Sometime(gd)
        }),
        map(
            tuple((tag("within"), cut(digit1), cut(gd))),
            |((), number, gd)| {
                ConstraintGD::Within(i64::from_str_radix(number.src, 10).unwrap(), gd)
            },
        ),
        map(pair(tag("at-most-once"), cut(gd)), |((), gd)| {
            ConstraintGD::AtMostOnce(gd)
        }),
        map(
            tuple((tag("sometime-after"), cut(gd), cut(gd))),
            |((), left, right)| ConstraintGD::SometimeAfter(left, right),
        ),
        map(
            tuple((tag("sometime-before"), cut(gd), cut(gd))),
            |((), left, right)| ConstraintGD::SometimeBefore(left, right),
        ),
        map(
            tuple((tag("always-within"), cut(digit1), cut(gd), cut(gd))),
            |((), number, left, right)| {
                ConstraintGD::AlwaysWithin(
                    i64::from_str_radix(number.src, 10).unwrap(),
                    left,
                    right,
                )
            },
        ),
        map(
            tuple((tag("hold-during"), cut(digit1), cut(digit1), cut(gd))),
            |((), val, res, gd)| {
                ConstraintGD::HoldDuring(
                    i64::from_str_radix(val.src, 10).unwrap(),
                    i64::from_str_radix(res.src, 10).unwrap(),
                    gd,
                )
            },
        ),
        map(
            tuple((tag("hold-after"), cut(digit1), cut(gd))),
            |((), number, gd)| {
                ConstraintGD::HoldAfter(i64::from_str_radix(number.src, 10).unwrap(), gd)
            },
        ),
    ))(input)
}

#[inline]
fn metric_spec(input: Input) -> IResult<Metric> {
    alt((
        map(pair(tag("minimize"), cut(metric_f_exp)), |((), mfe)| {
            Metric::Minimize(mfe)
        }),
        map(pair(tag("maximize"), cut(metric_f_exp)), |((), mfe)| {
            Metric::Maximize(mfe)
        }),
    ))(input)
}

#[inline]
fn metric_f_exp(input: Input) -> IResult<MetricFluentExpr> {
    alt((
        map(tag("total-time"), |_| MetricFluentExpr::TotalTime()),
        map(parens(pair(tag("is-violated"), cut(name))), |((), name)| {
            MetricFluentExpr::IsViolated(name)
        }),
        map(f_exp, |f| MetricFluentExpr::FExpr(f)),
    ))(input)
}

#[cfg(test)]
mod tests {
    use super::ast::Span;
    use super::*;

    #[test]
    fn test_basic() {
        assert_eq!(
            pddl_anyletter(Input::new(false, "H_ i")),
            Ok((
                Input {
                    // filename: None,
                    src: " i",
                    is_problem: false,
                    input_pos: 2,
                    requirements: EnumSet::EMPTY
                },
                Input::new(false, "H_")
            ))
        );
        assert_eq!(
            name(Input::new(true, "He-l_lo world")),
            Ok((
                Input {
                    // filename: None,
                    src: "world",
                    is_problem: true,
                    input_pos: 8,
                    requirements: EnumSet::EMPTY
                },
                Name::new(0..7, "He-l_lo")
            ))
        );
        assert_eq!(
            name(Input::new(false, "He-l_lo world")).unwrap().1 .0,
            (0..7).into()
        );
        let mut span: Span = (0..0).into();
        span.is_problem = true;
        assert_eq!(
            name(Input::new(true, "#$Hello")),
            Err(nom::Err::Error(Error {
                // input: Some("#$Hello"),
                kind: ErrorKind::Name,
                chain: None,
                span
            }))
        );
        assert_eq!(
            variable(Input::new(false, "?test me")),
            Ok((
                Input {
                    // filename: None,
                    is_problem: false,
                    src: "me",
                    input_pos: 6,
                    requirements: EnumSet::EMPTY
                },
                Name::new(0..5, "test")
            ))
        );
        assert_eq!(
            parens(name)(Input::new(false, "(test;comment\n)")),
            Ok((
                Input {
                    // filename: None,
                    is_problem: false,
                    src: "",
                    input_pos: 15,
                    requirements: EnumSet::EMPTY
                },
                Name::new(1..5, "test")
            ))
        );

        assert_eq!(
            pair(name, variable)(Input::new(false, "hello ?world")),
            Ok((
                Input {
                    // filename: None,
                    is_problem: false,
                    src: "",
                    input_pos: 12,
                    requirements: EnumSet::EMPTY
                },
                (Name::new(0..5, "hello"), Name::new(6..12, "world"))
            ))
        );

        assert_eq!(
            term(Input {
                // filename: None,
                is_problem: true,
                src: "(test ?one)  ",
                input_pos: 0,
                requirements: enum_set!(ObjectFluents)
            }),
            Ok((
                Input {
                    is_problem: true,
                    // filename: None,
                    src: "",
                    input_pos: 13,
                    requirements: enum_set!(ObjectFluents)
                },
                Term::Function(FunctionTerm {
                    name: Name::new(1..5, "test"),
                    terms: vec![Term::Variable(Name::new(6..10, "one"))]
                })
            ))
        );
        assert_eq!(
            term(Input {
                is_problem: false,
                src: "(test ?one)  ",
                input_pos: 0,
                requirements: enum_set!(ObjectFluents)
            })
            .unwrap()
            .1
            .span(),
            (1..10).into()
        );
        let mut span: Span = (0..13).into();
        span.is_problem = true;
        let test = Error {
            kind: ErrorKind::Term,
            chain: Some(Box::new(Error {
                kind: ErrorKind::UnsetRequirement(enum_set!(ObjectFluents)),
                chain: None,
                span,
            })),
            span,
        };
        // test.clone().report("stdio").eprint(("stdio", ariadne::Source::from("(test ?one)  ")));
        assert_eq!(
            term(Input::new(true, "(test ?one)  ")),
            Err(nom::Err::Error(test))
        );
        assert_eq!(
            term(Input::new(false, "?hello")),
            Ok((
                Input {
                    is_problem: false,
                    src: "",
                    input_pos: 6,
                    requirements: EnumSet::EMPTY
                },
                Term::Variable(Name::new(0..6, "hello"))
            ))
        );
        assert_eq!(
            typed_list(name)(Input {
                is_problem: false,
                src: "one two - object",
                input_pos: 0,
                requirements: enum_set!(Typing)
            }),
            Ok((
                Input {
                    is_problem: false,
                    src: "",
                    input_pos: 16,
                    requirements: enum_set!(Typing)
                },
                vec![List {
                    items: vec![Name::new(0..3, "one"), Name::new(4..7, "two")],
                    kind: Type::Exact(Name::new(10..16, "object"))
                }]
            ))
        );
        assert_eq!(
            typed_list(name)(Input::new(false, "one two")),
            Ok((
                Input {
                    is_problem: false,
                    src: "",
                    input_pos: 7,
                    requirements: EnumSet::EMPTY
                },
                vec![List {
                    items: vec![Name::new(0..3, "one"), Name::new(4..7, "two")],
                    kind: Type::None
                }]
            ))
        );
        assert_eq!(
            typed_list(variable)(Input::new(false, "?a1")),
            Ok((
                Input {
                    is_problem: false,
                    src: "",
                    input_pos: 3,
                    requirements: EnumSet::EMPTY
                },
                vec![List {
                    items: vec![Name::new(0..3, "a1")],
                    kind: Type::None
                }]
            ))
        );
        assert_eq!(
            atomic_function_skeleton(Input::new(false, "(testing ?left ?right)")),
            Ok((
                Input {
                    is_problem: false,
                    src: "",
                    input_pos: 22,
                    requirements: EnumSet::EMPTY
                },
                AtomicFSkeleton {
                    name: Name::new(1..8, "testing"),
                    variables: vec![List {
                        items: vec![Name::new(9..14, "left"), Name::new(15..21, "right")],
                        kind: Type::None
                    }]
                }
            ))
        )
    }

    #[test]
    fn test_typed_list() {
        assert_eq!(
            typed_list(variable)(Input::new(false, "?one ?two")),
            Ok((
                Input {
                    is_problem: false,
                    src: "",
                    input_pos: 9,
                    requirements: EnumSet::EMPTY
                },
                vec![List {
                    items: vec![Name::new(0..4, "one"), Name::new(5..9, "two")],
                    kind: Type::None
                }]
            ))
        );
    }

    #[test]
    fn test_atomic_formula() {
        assert_eq!(
            atomic_formula(term)(Input::new(false, "(ball ?obj)")),
            Ok((
                Input {
                    is_problem: false,
                    src: "",
                    input_pos: 11,
                    requirements: EnumSet::EMPTY
                },
                AtomicFormula::Predicate(
                    Name::new(1..5, "ball"),
                    vec![Term::Variable(Name::new(6..10, "obj"))]
                )
            ))
        )
    }

    #[test]
    fn test_gd() {
        assert_eq!(
            gd(Input::new(false, "(and (ball ?obj))")),
            Ok((
                Input {
                    is_problem: false,
                    src: "",
                    input_pos: 17,
                    requirements: EnumSet::EMPTY
                },
                GD::And(vec![GD::AtomicFormula(AtomicFormula::Predicate(
                    Name::new(6..10, "ball"),
                    vec![Term::Variable(Name::new(11..15, "obj"))]
                ))])
            ))
        )
    }

    #[test]
    fn test_effect() {
        assert!(empty_or(effect)(Input::new(
            false,
            "(and (at-robby ?to) (not (at-robby ?from)))"
        ))
        .is_ok())
    }
}
