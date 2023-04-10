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
    pub constants: Vec<TypedList<'a>>,
    pub predicates: Vec<CallableDeclaration<'a>>,
    pub functions: Vec<TypedFunction<'a>>,
    pub constraints: Option<Expr<'a>>,
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
pub enum Expr<'a> {
    And(Vec<Expr<'a>>),
    Or(Vec<Expr<'a>>),
    Not(Box<Expr<'a>>),
    Call{function:&'a str, variables:Vec<&'a str>}, // :object-fluents
    Subtract(Box<Expr<'a>>, Box<Expr<'a>>), // :numeric-fluents
    Add(Box<Expr<'a>>, Vec<Expr<'a>>), // :numeric-fluents
    Divide(Box<Expr<'a>>, Box<Expr<'a>>), // :numeric-fluents
    Multiply(Box<Expr<'a>>, Vec<Expr<'a>>), // :numeric-fluents
    LessThan(Box<Expr<'a>>, Box<Expr<'a>>), // :numeric-fluents
    LessThanOrEquals(Box<Expr<'a>>, Box<Expr<'a>>),
    Equals(Box<Expr<'a>>, Box<Expr<'a>>),
    BiggerThan(Box<Expr<'a>>, Box<Expr<'a>>),
    BiggerThanOrEquals(Box<Expr<'a>>, Box<Expr<'a>>),
    Imply(Box<Expr<'a>>, Box<Expr<'a>>),
    Exists{variables:TypedList<'a>, expr:Box<Expr<'a>>},
    Forall{variables:TypedList<'a>, expr:Box<Expr<'a>>}, // :conditional−effects
    Preference{name: &'a str, expr:Box<Expr<'a>>},
    When{condition:Box<Expr<'a>>, effect:Box<Expr<'a>>}, // :conditional−effects
    AtomicFormula{predicate:&'a str, term:Vec<&'a str>},
    Literal{name:&'a str, variables:Vec<&'a str>}
}

#[derive(PartialEq, Debug)]
pub enum Action<'a> {
    Basic(BasicAction<'a>),
    Durative{a:BasicAction<'a>, duration:Expr<'a>},
    Derived{predicate:CallableDeclaration<'a>, expr:Expr<'a>}
}

#[derive(PartialEq, Debug)]
pub struct BasicAction<'a> {
    pub name:&'a str, 
    pub parameters: Vec<TypedList<'a>>, 
    pub precondition:Option<Expr<'a>>, 
    pub effect:Option<Expr<'a>>
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
pub struct CallableDeclaration<'a> {
    pub name: &'a str,
    pub variables: Vec<TypedList<'a>>
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
    pub function: CallableDeclaration<'a>,
    pub kind: FunctionTypeKind<'a>
}

#[derive(PartialEq, Debug)]
pub struct TypedList<'a> {
    pub identifiers: Vec<&'a str>,
    /// kind will be None if `:typing` is not required
    pub kind:Option<&'a str>, 
}
