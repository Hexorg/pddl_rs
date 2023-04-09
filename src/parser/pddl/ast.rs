use enumset::{EnumSet, EnumSetType};

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
    pub objects: Vec<TypedList<'a>>,
    pub init: Expr<'a>,
    pub goal: Expr<'a>,
    // pub constraints: &'a str,
    // pub metric: &'a str,
    // pub length: &'a str
}

#[derive(PartialEq, Debug)]
pub struct Domain<'a> {
    pub name: &'a str,
    pub requirements: EnumSet<Requirements>,
    pub types: Vec<TypedList<'a>>,
    // pub constants: TypedList<'a>,
    pub predicates: Vec<Predicate<'a>>,
    // pub functions: &'a str,
    // pub constraints: &'a str,
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
    /// Allow `or` in goal descriptions
    DisjunctivePreconditions,
    /// Support `=` as built-in predicate
    Equality,
    /// Allow `exists` in goal descriptions
    ExistentialPreconditions,
    /// Allow `forall` in goal descriptions
    UniversalPreconditions,
    /// Same as `:existential-preconditions` + 
    /// `:universal-preconditions`
    QuantifiedPreconditions,
    /// Allow when in action effects
    ConditionalEffects,
    /// Allow function definitions and use of effects using assignment operators and arithmetic preconditions.
    Fluents,
    /// Same as `:strips` + `:typing` + `:negative-preconditions` + 
    /// `:disjunctive-preconditions` + `:equality` + 
    /// `:quantified-preconditions` + `:conditional-effects`
    ADL,
    /// Allows durative actions.
    /// 
    /// Note: that this does not imply `:fluents`
    DurativeActions,
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
    Constraints
}

#[derive(PartialEq, Debug)]
pub enum Expr<'a> {
    And(Vec<Expr<'a>>),
    Not(Box<Expr<'a>>),
    Literal{name:&'a str, variables:Vec<&'a str>}
}

#[derive(PartialEq, Debug)]
pub struct Action<'a> {
    pub name: &'a str,
    pub parameters: Vec<TypedList<'a>>,
    pub precondition: Option<Expr<'a>>,
    pub effect: Option<Expr<'a>>
}

#[derive(PartialEq, Debug)]
pub struct Predicate<'a> {
    pub name: &'a str,
    pub variables: Vec<TypedList<'a>>
}

#[derive(PartialEq, Debug)]
pub struct TypedList<'a> {
    pub identifiers: Vec<&'a str>,
    /// kind will be None if `:typing` is not required
    pub kind:Option<&'a str>, 
}
