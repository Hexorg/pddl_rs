use enumset::{EnumSet, EnumSetType};

use super::tokens::Literal;

#[derive(PartialEq, Debug)]
pub enum Stmt<'a> {
    Domain(Domain<'a>),
    Problem(Problem<'a>)
}

impl<'a> Stmt<'a> {
    pub fn unwrap_domain(self) -> Domain<'a> {
        match self {
            Self::Domain(d) => d,
            _ => panic!(),
        }
    }

    pub fn unwrap_problem(self) -> Problem<'a> {
        match self {
            Self::Problem(p) => p,
            _ => panic!(),
        }
    }
}

#[derive(PartialEq, Debug)]
pub struct Problem<'a> {
    pub name: &'a str,
    pub domain: &'a str,
    pub requirements: EnumSet<Requirements>,
    pub objects: Vec<List<'a>>,
    pub init: Vec<Init<'a>>,
    pub goal: PreconditionExpr<'a>,
    pub constraints: Option<PrefConstraintGD<'a>>,
    pub metric: Option<Metric<'a>>,
    pub length: Option<LengthSpecification<'a>>
}

#[derive(PartialEq, Debug)]
pub struct LengthSpecification<'a> {
    serial: Option<Literal<'a>>,
    parallel: Option<Literal<'a>>
}


#[derive(PartialEq, Debug)]
pub struct Domain<'a> {
    pub name: &'a str,
    pub requirements: EnumSet<Requirements>,
    pub types: Vec<List<'a>>,
    pub constants: Vec<List<'a>>,
    pub predicates: Vec<AtomicFSkeleton<'a>>,
    pub functions: Vec<TypedFunction<'a>>,
    pub constraints: Option<ConstraintGD<'a>>,
    pub actions: Vec<Action<'a>>,
}

#[derive(EnumSetType, Debug)]
pub enum Requirements {
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

impl std::fmt::Display for Requirements {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Requirements::Strips => write!(f, ":strips"),
            Requirements::Typing => write!(f, ":typing"),
            Requirements::NegativePreconditions => write!(f, ":negative-preconditions"),
            Requirements::DisjunctivePreconditions => write!(f, ":disjunctive-preconditions"),
            Requirements::Equality => write!(f, ":equality"),
            Requirements::ExistentialPreconditions => write!(f, ":existential-preconditions"),
            Requirements::UniversalPreconditions => write!(f, ":universal-preconditions"),
            Requirements::ConditionalEffects => write!(f, ":conditional-effects"),
            Requirements::ObjectFluents => write!(f, ":fluents"),
            Requirements::NumericFluents => write!(f, ":numeric-fluents"),
            Requirements::DurativeActions => write!(f, ":durative-actions"),
            Requirements::DurationInequalities => write!(f, ":duration-inequalities"),
            Requirements::ContinuousEffects => write!(f, ":continuous-effects"),
            Requirements::DerivedPredicates => write!(f, ":derived-predicates"),
            Requirements::TimedInitialLiterals => write!(f, ":timed-initial-literals"),
            Requirements::Preferences => write!(f, ":preferences"),
            Requirements::Constraints => write!(f, ":constraints"),
            Requirements::ActionCosts => write!(f, ":action-costs"),
        }
    }
}

#[derive(PartialEq, Debug)]
pub enum PreconditionExpr<'a> {
    And(Vec<PreconditionExpr<'a>>),
    Forall(Vec<List<'a>>, Box<PreconditionExpr<'a>>), // :universal−preconditions or // :conditional−effects
    Preference(Option<&'a str>, GD<'a>), // :preferences
    GD(GD<'a>)
}

#[derive(PartialEq, Debug)]
pub enum GD<'a> {
    AtomicFormula(&'a str, Vec<Term<'a>>),
    AtomicEquality(Term<'a>, Term<'a>), // :equality
    NotAtomicFormula(&'a str, Vec<Term<'a>>), // :negative−preconditions
    NotAtomicEquality(Term<'a>, Term<'a>), // :equality AND :negative−preconditions
    And(Vec<GD<'a>>), // not(and(f1, f2, f2)) is legal, but not(and(Preference, Preference, Preference)) is not, 
                      // however and(Preference, Preference, Preference) is legal. That's why GD has And too.
    Or(Vec<GD<'a>>), //:disjunctive−preconditions
    Not(Box<GD<'a>>), // :disjunctive−preconditions
    Imply(Box<(GD<'a>, GD<'a>)>), // :disjunctive−preconditions
    Exists(Vec<List<'a>>, Box<GD<'a>>), // :existential−preconditions
    Forall(Vec<List<'a>>, Box<GD<'a>>), // :universal−preconditions
    
    LessThan(FluentExpression<'a>, FluentExpression<'a>), // :numeric-fluents
    LessThanOrEqual(FluentExpression<'a>, FluentExpression<'a>), // :numeric-fluents
    Equal(FluentExpression<'a>, FluentExpression<'a>), // :numeric-fluents
    GreatherThanOrEqual(FluentExpression<'a>, FluentExpression<'a>), // :numeric-fluents
    GreaterThan(FluentExpression<'a>, FluentExpression<'a>), // :numeric-fluents
}

#[derive(PartialEq, Debug)]
pub enum FluentExpression<'a> {
    Number(Literal<'a>), // :numeric-fluents
    Subtract(Box<(FluentExpression<'a>, FluentExpression<'a>)>), // :numeric-fluents
    Divide(Box<(FluentExpression<'a>, FluentExpression<'a>)>), // :numeric-fluents
    Add(Vec<FluentExpression<'a>>), // :numeric-fluents
    Multiply(Vec<FluentExpression<'a>>), // :numeric-fluents
    Function(FunctionTerm<'a>), // :numeric-fluents
}

#[derive(PartialEq, Debug)]
pub enum Effect<'a> {
    And(Vec<Effect<'a>>),
    Forall(Vec<List<'a>>, Box<Effect<'a>>), // :conditional−effects
    When(GD<'a>, Vec<Effect<'a>>), // :conditional−effects
    AtomicFormula(&'a str, Vec<Term<'a>>),
    NotAtomicFormula(&'a str, Vec<Term<'a>>),
    Assign(FunctionTerm<'a>, FluentExpression<'a>), // :numeric-fluents
    AssignUndefined(FunctionTerm<'a>), // :object-fluents
    ScaleUp(FunctionTerm<'a>, FluentExpression<'a>), // :numeric-fluents
    ScaleDown(FunctionTerm<'a>, FluentExpression<'a>), // :numeric-fluents
    Increase(FunctionTerm<'a>, FluentExpression<'a>), // :numeric-fluents
    Decrease(FunctionTerm<'a>, FluentExpression<'a>), // :numeric-fluents
}

#[derive(PartialEq, Debug)]
pub enum DurationConstraint<'a> {
    And(Vec<DurationConstraint<'a>>), // :duration−inequalities
    AtStart(Box<DurationConstraint<'a>>), 
    AtEnd(Box<DurationConstraint<'a>>),
    GreaterOrEquals(FluentExpression<'a>), // :duration−inequalities
    LessThanOrEquals(FluentExpression<'a>), // :duration−inequalities
    Equals(FluentExpression<'a>),
}

#[derive(PartialEq, Debug)]
pub enum DurationGD<'a> {
    And(Vec<DurationGD<'a>>),
    Forall(Vec<List<'a>>, Box<DurationGD<'a>>), // :universal−preconditions
    Preference(Option<&'a str>, TimedGD<'a>), // :preferences
    GD(TimedGD<'a>)
}

#[derive(PartialEq, Debug)]
pub enum DurationEffect<'a> {
    And(Vec<DurationEffect<'a>>),
    Forall(Vec<List<'a>>, Box<DurationEffect<'a>>), // :universal−preconditions
    When(DurationGD<'a>, TimedEffect<'a>), // :conditional−effects
    GD(TimedEffect<'a>),
}

#[derive(PartialEq, Debug)]
pub enum PrefConstraintGD<'a> {
    And(Vec<PrefConstraintGD<'a>>),
    Forall(Vec<List<'a>>, Box<PrefConstraintGD<'a>>), // :universal−preconditions
    Preference(&'a str, ConstraintGD<'a>), // :preferences
    GD(ConstraintGD<'a>)
}

#[derive(PartialEq, Debug)]
pub enum ConstraintGD<'a> {
    And(Vec<ConstraintGD<'a>>),
    Forall(Vec<List<'a>>, Box<ConstraintGD<'a>>),
    AtEnd(GD<'a>),
    Always(GD<'a>),
    Sometime(GD<'a>),
    Within(Literal<'a>, GD<'a>),
    AtMostOnce(GD<'a>),
    SometimeAfter(GD<'a>, GD<'a>),
    SometimeBefore(GD<'a>, GD<'a>),
    AlwaysWithin(Literal<'a>, GD<'a>, GD<'a>),
    HoldDuring(Literal<'a>, Literal<'a>, GD<'a>),
    HoldAfter(Literal<'a>, GD<'a>)
}


#[derive(PartialEq, Debug)]
pub enum TimedEffect<'a> {
    AtStart(Effect<'a>),
    AtEnd(Effect<'a>),
    Effect(Effect<'a>)
}

#[derive(PartialEq, Debug)]
pub enum Init<'a> {
    AtomicFormula(&'a str, Vec<Term<'a>>),
    NotAtomicFormula(&'a str, Vec<Term<'a>>), // :negative−preconditions
    At(Literal<'a>, Vec<Term<'a>>), // :timed−initial−literals
    NotAt(Literal<'a>, Vec<Term<'a>>), // :timed−initial−literals
    Equals(FunctionTerm<'a>, Literal<'a>), // :numeric-fluents
    Is(FunctionTerm<'a>, Term<'a>), // :object-fluents
}

#[derive(PartialEq, Debug)]
pub enum TimedGD<'a> {
    AtStart(GD<'a>),
    AtEnd(GD<'a>),
    OverAll(GD<'a>)
}

#[derive(PartialEq, Debug)]
pub enum MetricFluentExpr<'a> {
    FExpr(FluentExpression<'a>),
    TotalTime(),
    IsViolated(&'a str)
}

#[derive(PartialEq, Debug)]
pub enum Metric<'a> {
    Minimize(MetricFluentExpr<'a>),
    Maximize(MetricFluentExpr<'a>)
}

#[derive(PartialEq, Debug)]
pub enum Action<'a> {
    Basic(BasicAction<'a>),
    Durative(DurativeAction<'a>), // :durative−actions
    Derived(AtomicFSkeleton<'a>, GD<'a>) // :derived−predicates
}

#[derive(PartialEq, Debug)]
pub struct BasicAction<'a> {
    pub name:&'a str, 
    pub parameters: Vec<List<'a>>, 
    pub precondition:Option<PreconditionExpr<'a>>, 
    pub effect:Option<Effect<'a>>
}

#[derive(PartialEq, Debug)]
pub struct DurativeAction<'a> {
    pub name:&'a str, 
    pub parameters: Vec<List<'a>>, 
    pub duration: DurationConstraint<'a>,
    pub condition: Option<DurationGD<'a>>, 
    pub effect:Option<DurationEffect<'a>>
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
pub struct AtomicFSkeleton<'a> {
    pub name: &'a str,
    pub variables: Vec<List<'a>>
}


/// [`FunctionTypeKind::Numeric`] if `:numeric-fluents` is set.
#[derive(PartialEq, Debug)]
pub enum FunctionTypeKind<'a> {
    None,
    Numeric(i64),
    Typed(Vec<&'a str>)
}

#[derive(PartialEq, Debug)]
pub struct TypedFunction<'a> {
    pub function: AtomicFSkeleton<'a>,
    pub kind: FunctionTypeKind<'a>
}

#[derive(PartialEq, Debug)]
pub enum List<'a> {
    Basic(Vec<&'a str>),
    Typed(Vec<&'a str>, &'a str),
}

#[derive(PartialEq, Debug)]
pub struct FunctionTerm<'a> {
    pub name:&'a str,
    pub terms: Vec<Term<'a>>
}
#[derive(PartialEq, Debug)]
pub enum Term<'a> {
    Name(&'a str),
    Variable(&'a str),
    Function(FunctionTerm<'a>) // :object-fluents
}