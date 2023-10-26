use std::ops::Range;

use enumset::{EnumSet, EnumSetType};

pub trait SpannedAst {
    fn range(&self) -> Range<usize>;
}

pub trait SpannedAstMut: SpannedAst {
    fn range_mut(&mut self) -> &mut Range<usize>;
}
impl<O> SpannedAst for Spanned<O> {
    #[inline]
    fn range(&self) -> Range<usize> {
        self.0.clone()
    }
}
impl<O> SpannedAstMut for Spanned<O> {
    #[inline]
    fn range_mut(&mut self) -> &mut Range<usize> {
        &mut self.0
    }
}

pub type Spanned<O> = (Range<usize>, O);
pub type Name<'src> = Spanned<&'src str>;

impl<O> SpannedAst for Vec<O>
where
    O: SpannedAst,
{
    fn range(&self) -> Range<usize> {
        let start = self
            .first()
            .and_then(|r| Some(r.range().start))
            .unwrap_or(0);
        let end = self
            .last()
            .and_then(|r| Some(r.range().end))
            .unwrap_or(start);
        Range { start, end }
    }
}

#[derive(PartialEq, Debug)]
pub struct Problem<'src> {
    pub name: Name<'src>,
    pub domain: Name<'src>,
    pub requirements: EnumSet<Requirement>,
    pub objects: Vec<List<'src>>,
    pub init: Vec<Init<'src>>,
    pub goal: PreconditionExpr<'src>,
    pub constraints: Option<PrefConstraintGD<'src>>,
    pub metric: Option<Metric<'src>>,
    // pub length: Option<LengthSpecification>, // deprecated since PDDL 2.1
}

#[derive(PartialEq, Debug)]
pub struct Domain<'src> {
    pub name: Name<'src>,
    pub requirements: EnumSet<Requirement>,
    pub types: Vec<List<'src>>,
    pub constants: Vec<List<'src>>,
    pub predicates: Vec<AtomicFSkeleton<'src>>,
    pub functions: Vec<FunctionTypedList<'src>>,
    pub constraints: Option<ConstraintGD<'src>>,
    pub actions: Vec<Action<'src>>,
}

#[derive(EnumSetType, Debug)]
pub enum Requirement {
    /// Basic STRIPS-style adds and deletes
    Strips,
    /// Allow type names in declarations of variables
    Typing,
    /// Allow `not` in goal descriptions
    NegativePreconditions,
    /// Allow `or` in goal descriptions
    DisjunctivePreconditions,
    /// Support `=` as built-in predicate
    Equality,
    /// Allow `exists` in goal descriptions
    ExistentialPreconditions,
    /// Allow `forall` in goal descriptions
    UniversalPreconditions,
    /// Allow when in action effects
    ConditionalEffects,
    /// Allow function definitions and use of effects using assignment operators and arithmetic preconditions.
    ObjectFluents,
    /// Allow numeric function definitions and use of effects using assignment operators and arithmetic preconditions.
    NumericFluents,
    /// Allows durative actions.
    ///
    /// Note: that this does not imply `:numeric-fluents`
    DurativeActions,
    /// Allows duration constraints in durative actions using inequalities.
    DurationInequalities,
    /// Allows durative actions to affect fluents continuously over the duration of the actions.
    ContinuousEffects,
    /// Allows predicates whose truth value is defined by a formula
    DerivedPredicates,
    /// Allows the initial state to specify literals
    /// that will become true at a specified time point
    /// implies [DurativeActions]
    TimedInitialLiterals,
    /// Allows use of preferences in action
    /// preconditions and goals.
    Preferences,
    /// Allows use of constraints fields in
    /// domain and problem files. These may contain modal operators supporting trajectory
    /// constraints.
    Constraints,
    /// If this requirement is included in a PDDL specification,
    /// the use of numeric fluents is enabled (similar to the
    /// `:numeric-fluents` requirement). However, numeric fluents
    /// may only be used in certain very limited ways:
    /// 1. Numeric fluents may not be used in any conditions (preconditions, goal conditions,
    /// conditions of conditional effects, etc.).
    /// 2. A numeric fluent may only be used as the target of an effect if it is 0-ary and called `total-cost`.
    /// If such an effect is used, then the `total-cost` fluent must be explicitly initialized
    /// to 0 in the initial state.
    /// 3. The only allowable use of numeric fluents in effects is in effects of the form
    /// `(increase (total-cost) <numeric-term>)`, where the `<numeric-term>` is either
    /// a non-negative numeric constant or of the form `(<function-symbol> <term>*)`.
    /// (The `<term>` here is interpreted as shown in the PDDL grammar, i.e.
    /// it is a variable symbol or an object constant. Note that this `<term>` cannot
    /// be a `<function-term>`, even if the object fluents requirement is used.)
    /// 4. No numeric fluent may be initialized to a negative value.
    /// 5. If the problem contains a `:metric` specification, the objective must
    /// be `(minimize (total-cost))`, or - only if the `:durative-actions` requirement
    /// is also set - to minimize a linear combination of `total-cost` and `total-time`,
    /// with non-negative coefficients.
    ///
    /// Note that an action can have multiple effects that increase `(total-cost)`, which
    /// is particularly useful in the context of conditional effects.
    /// Also note that these restrictions imply that `(total-cost)` never
    /// decreases throughout plan execution, i.e., action costs are never negative.
    ActionCosts,
}

impl std::fmt::Display for Requirement {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Requirement::Strips => write!(f, ":strips"),
            Requirement::Typing => write!(f, ":typing"),
            Requirement::NegativePreconditions => write!(f, ":negative-preconditions"),
            Requirement::DisjunctivePreconditions => write!(f, ":disjunctive-preconditions"),
            Requirement::Equality => write!(f, ":equality"),
            Requirement::ExistentialPreconditions => write!(f, ":existential-preconditions"),
            Requirement::UniversalPreconditions => write!(f, ":universal-preconditions"),
            Requirement::ConditionalEffects => write!(f, ":conditional-effects"),
            Requirement::ObjectFluents => write!(f, ":fluents"),
            Requirement::NumericFluents => write!(f, ":numeric-fluents"),
            Requirement::DurativeActions => write!(f, ":durative-actions"),
            Requirement::DurationInequalities => write!(f, ":duration-inequalities"),
            Requirement::ContinuousEffects => write!(f, ":continuous-effects"),
            Requirement::DerivedPredicates => write!(f, ":derived-predicates"),
            Requirement::TimedInitialLiterals => write!(f, ":timed-initial-literals"),
            Requirement::Preferences => write!(f, ":preferences"),
            Requirement::Constraints => write!(f, ":constraints"),
            Requirement::ActionCosts => write!(f, ":action-costs"),
        }
    }
}

#[derive(PartialEq, Debug)]
pub struct Forall<'src, T> {
    pub variables: Vec<List<'src>>,
    pub gd: Box<T>,
}

#[derive(PartialEq, Debug)]
pub struct When<T, P> {
    pub gd: T,
    pub effect: Box<P>,
}

#[derive(PartialEq, Debug)]
pub struct Preference<'src, T> {
    pub name: Option<Name<'src>>,
    pub gd: T,
}

pub type Exists<'src, T> = Forall<'src, T>;

/// AST Representation of preconditions.
#[derive(PartialEq, Debug)]
pub enum PreconditionExpr<'src> {
    And(Vec<PreconditionExpr<'src>>),
    Forall(Forall<'src, Self>), // :universal−preconditions or // :conditional−effects
    Preference(Preference<'src, GD<'src>>), // :preferences
    GD(GD<'src>),
}

#[derive(PartialEq, Debug)]
pub enum GD<'src> {
    AtomicFormula(AtomicFormula<'src, Term<'src>>),
    And(Vec<GD<'src>>), // not(and(f1, f2, f2)) is legal, but not(and(Preference, Preference, Preference)) is not,
    // however and(Preference, Preference, Preference) is legal. That's why GD has And too.
    Or(Vec<GD<'src>>),                //:disjunctive−preconditions
    Not(Box<GD<'src>>),               // :disjunctive−preconditions
    Imply(Box<(GD<'src>, GD<'src>)>), // :disjunctive−preconditions
    Exists(Exists<'src, Self>),       // :existential−preconditions
    Forall(Forall<'src, Self>),       // :universal−preconditions

    LessThan(FluentExpression<'src>, FluentExpression<'src>), // :numeric-fluents
    LessThanOrEqual(FluentExpression<'src>, FluentExpression<'src>), // :numeric-fluents
    Equal(FluentExpression<'src>, FluentExpression<'src>),    // :numeric-fluents
    GreatherThanOrEqual(FluentExpression<'src>, FluentExpression<'src>), // :numeric-fluents
    GreaterThan(FluentExpression<'src>, FluentExpression<'src>), // :numeric-fluents
}

#[derive(PartialEq, Debug)]
pub enum FluentExpression<'src> {
    Number(i64),                                   // :numeric-fluents
    Subtract(Box<(Spanned<Self>, Spanned<Self>)>), // :numeric-fluents
    Negate(Box<Spanned<Self>>),
    Divide(Box<(Spanned<Self>, Spanned<Self>)>), // :numeric-fluents
    Add(Vec<Spanned<Self>>),                     // :numeric-fluents
    Multiply(Vec<Spanned<Self>>),                // :numeric-fluents
    Function(FunctionTerm<'src>),                // :numeric-fluents
}

#[derive(PartialEq, Debug)]
pub enum Effect<'src> {
    And(Vec<Self>),
    Forall(Forall<'src, Self>), // :conditional−effects
    When(When<GD<'src>, Self>), // :conditional−effects
    NegativeFormula(NegativeFormula<'src, Term<'src>>),
    Assign(FunctionTerm<'src>, Spanned<FluentExpression<'src>>), // :numeric-fluents
    AssignTerm(FunctionTerm<'src>, Term<'src>),
    AssignUndefined(FunctionTerm<'src>), // :object-fluents
    ScaleUp(FunctionTerm<'src>, Spanned<FluentExpression<'src>>), // :numeric-fluents
    ScaleDown(FunctionTerm<'src>, Spanned<FluentExpression<'src>>), // :numeric-fluents
    Increase(FunctionTerm<'src>, Spanned<FluentExpression<'src>>), // :numeric-fluents
    Decrease(FunctionTerm<'src>, Spanned<FluentExpression<'src>>), // :numeric-fluents
}

#[derive(PartialEq, Debug)]
pub enum DurationConstraint<'src> {
    None,
    And(Vec<Self>), // :duration−inequalities
    AtStart(Box<Self>),
    AtEnd(Box<Self>),
    GreaterOrEquals(Spanned<FluentExpression<'src>>), // :duration−inequalities
    LessThanOrEquals(Spanned<FluentExpression<'src>>), // :duration−inequalities
    Equals(Spanned<FluentExpression<'src>>),
}

#[derive(PartialEq, Debug)]
pub enum DurationGD<'src> {
    And(Vec<Self>),
    Forall(Forall<'src, Self>), // :universal−preconditions
    Preference(Preference<'src, TimedGD<'src>>), // :preferences
    GD(TimedGD<'src>),
}

#[derive(PartialEq, Debug)]
pub enum DurationEffect<'src> {
    And(Vec<Self>),
    Forall(Forall<'src, Self>), // :universal−preconditions
    When(When<DurationGD<'src>, TimedEffect<'src>>), // :conditional−effects
    GD(TimedEffect<'src>),
}

#[derive(PartialEq, Debug)]
pub enum PrefConstraintGD<'src> {
    And(Vec<Self>),
    Forall(Forall<'src, Self>), // :universal−preconditions
    Preference(Preference<'src, ConstraintGD<'src>>), // :preferences
    GD(ConstraintGD<'src>),
}

#[derive(PartialEq, Debug)]
pub enum ConstraintGD<'src> {
    And(Vec<Self>),
    Forall(Forall<'src, Self>),
    AtEnd(GD<'src>),
    Always(GD<'src>),
    Sometime(GD<'src>),
    Within(i64, GD<'src>),
    AtMostOnce(GD<'src>),
    SometimeAfter(GD<'src>, GD<'src>),
    SometimeBefore(GD<'src>, GD<'src>),
    AlwaysWithin(i64, GD<'src>, GD<'src>),
    HoldDuring(i64, i64, GD<'src>),
    HoldAfter(i64, GD<'src>),
}

#[derive(PartialEq, Debug)]
pub enum TimedEffect<'src> {
    AtStart(Effect<'src>),
    AtEnd(Effect<'src>),
    Effect(Effect<'src>),
}

#[derive(PartialEq, Debug)]
pub enum Init<'src> {
    AtomicFormula(NegativeFormula<'src, Name<'src>>),
    At(i64, NegativeFormula<'src, Name<'src>>), // :timed−initial−literals
    Equals(FunctionTerm<'src>, i64),            // :numeric-fluents
    Is(FunctionTerm<'src>, Name<'src>),         // :object-fluents
}

#[derive(PartialEq, Debug)]
pub enum TimedGD<'src> {
    AtStart(GD<'src>),
    AtEnd(GD<'src>),
    OverAll(GD<'src>),
}

#[derive(PartialEq, Debug)]
pub enum MetricFluentExpr<'src> {
    FExpr(Spanned<FluentExpression<'src>>),
    TotalTime(),
    IsViolated(Name<'src>),
}

#[derive(PartialEq, Debug)]
pub enum Metric<'src> {
    Minimize(MetricFluentExpr<'src>),
    Maximize(MetricFluentExpr<'src>),
}

/// Action representation of PDDL 3.1. It's an enum with 3 variants:
/// * Basic([`BasicAction`])
/// * Durative([`DurativeAction`])
/// * Derived([`DerivedAction`])
#[derive(PartialEq, Debug)]
pub enum Action<'src> {
    Basic(BasicAction<'src>),
    Durative(DurativeAction<'src>),           // :durative−actions
    Derived(AtomicFSkeleton<'src>, GD<'src>), // :derived−predicates
}

/// Basic PDDL Action
#[derive(PartialEq, Debug)]
pub struct BasicAction<'src> {
    /// Human-readable name of this action.
    pub name: Name<'src>,
    /// Action parameters - similar to function parameters in programming
    /// They can be typed or not, depending on domain requirements.
    pub parameters: Vec<List<'src>>,
    /// AST representation of basic preconditions.
    pub precondition: Option<PreconditionExpr<'src>>,
    /// AST representation of basic effects.
    pub effect: Option<Effect<'src>>,
}

#[derive(PartialEq, Debug)]
pub struct DurativeAction<'src> {
    pub name: Name<'src>,
    pub parameters: Vec<List<'src>>,
    pub duration: DurationConstraint<'src>,
    pub condition: Option<DurationGD<'src>>,
    pub effect: Option<DurationEffect<'src>>,
}

/// Structure used for both Predicates and Functions
///
/// Predicates are defined as
/// ```ebnf
/// <atomic formula skeleton> ::= (<predicate> <typed list (variable)>)
/// <predicate> ::= <name>
/// ```
/// Functions are defined as
/// ```ebnf
/// <atomic function skeleton> ::= (<function-symbol> <typed list (variable)>)
/// <function-symbol> ::= <name>
/// ```
/// So they are really the same, just used differently.
#[derive(PartialEq, Debug)]
pub struct AtomicFSkeleton<'src> {
    pub name: Name<'src>,
    pub variables: Vec<List<'src>>,
}

#[derive(PartialEq, Debug)]
pub enum Type<'src> {
    None,
    Either(Vec<Name<'src>>),
    Exact(Name<'src>),
}

/// [`FunctionTypeKind::Numeric`] if `:numeric-fluents` is set.
#[derive(PartialEq, Debug)]
pub enum FunctionType<'src> {
    None,
    Numeric(Spanned<i64>),
    Typed(Type<'src>),
}

#[derive(PartialEq, Debug)]
pub struct FunctionTypedList<'src> {
    pub functions: Vec<AtomicFSkeleton<'src>>,
    pub kind: FunctionType<'src>,
}

#[derive(PartialEq, Debug)]
pub struct List<'src> {
    pub items: Vec<Name<'src>>,
    pub kind: Type<'src>,
}

#[derive(PartialEq, Debug, Hash, Eq, Clone)]
pub enum AtomicFormula<'src, T> {
    Predicate(Name<'src>, Vec<T>),
    Equality(T, T),
}

#[derive(PartialEq, Debug)]
pub enum NegativeFormula<'src, T> {
    Direct(AtomicFormula<'src, T>),
    Not(AtomicFormula<'src, T>),
}

/// Function name with 0 or more arguments
#[derive(PartialEq, Debug, Hash, Eq, Clone)]
pub struct FunctionTerm<'src> {
    pub name: Name<'src>,
    pub terms: Vec<Term<'src>>,
}

impl<'src> SpannedAst for FunctionTerm<'src> {
    fn range(&self) -> Range<usize> {
        self.name.0.start..self.terms.range().end
    }
}

/// A name, variable, or function
#[derive(PartialEq, Debug, Hash, Eq, Clone)]
pub enum Term<'src> {
    Name(Name<'src>),
    Variable(Name<'src>),
    Function(FunctionTerm<'src>), // :object-fluents
}

impl<'src> SpannedAst for Term<'src> {
    fn range(&self) -> Range<usize> {
        match self {
            Self::Name(n) => n.0.clone(),
            Self::Variable(v) => v.0.clone(),
            Self::Function(f) => f.range(),
        }
    }
}
