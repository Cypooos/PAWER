use crate::{definitions::*, manager::{Tactic,Command}};
use thiserror::Error;

// This file defines all the different errors that can be raised


// A generic Error enum, that is either an EvaluationError (user-generated one), an InternalError (more problematic!) or a Parsing one
#[derive(Error, Debug, PartialEq, Eq)]
pub enum Error {
    #[error(transparent)]
    EvaluationError(#[from] EvaluationError),
    #[error(transparent)]
    InternalError(#[from] InternalError),
    #[error("Parsing Error: {0}")]
    Parsing(String)
}

// All typing-related error (since there is a lot of them) are put in a different category in TypingError
#[derive(Error, Debug, PartialEq, Eq, Clone)]
pub enum EvaluationError {
    #[error("Typing Error: {0}")]
    TypingError(#[from] TypingError),
    #[error("No goals to apply tactic {0}")]
    NoMoreGoals(Tactic),
    #[error("Tactic exact failed the type matching with term {0} for goal {1}: {2}")]
    ExactMatching(LambdaTerm, String, TypingError),
    #[error("Check failed for term {0}: {1}")]
    CheckComm(LambdaTerm, TypingError),
    #[error("There are still unfinished goals.")]
    UnfinishedGoals,
    #[error("Can't start a new proof inside of another.")]
    AlreadyProof,
    #[error("Not in proof mode.")]
    NoProof,
    #[error("Cannot intro a non forall or implication (non-pi type).")]
    IntroNotPi,
    #[error("Too many intros requested, each introduction must correspond to a forall")]
    TooManyIntros,
    #[error("A theorem/definition with the name {0} already exists : {1}")]
    TheoremAlreadyExists(String, String),
    #[error("Cannot unfold `{0}` as it wasn't previously define/proven.")]
    UnfoldNotFound(String),
    #[error("Define can't infer the type for {0}: {1}")]
    DefineNotTypable(String,TypingError),
    #[error("Goal not found in lambda for tactic apply.")]
    ApplyGoalNotFound,
    #[error("Invalid arity in inductive definition.")]
    InvalidArity,
    #[error("Unknown variable `{0}` to perform induction on.")]
    UnknowVariableInduction(String),
    #[error("Variable `{0}` is not an inductive type.")]
    VariableNotInductive(String),
    #[error("Induction can (for now) only be done on arity 0 inductive types.")]
    InductiveArity0,
}

#[derive(Error, Debug, PartialEq, Eq, Clone)]
pub enum InternalError {
    #[error("Node at position `{0}` doesn't exists, but is pointed to")]
    NodeIncorrectPointer(NodeIndex),
    #[error("Lambda term contains a hole but shouldn't during call to `{0}`")]
    HoleContained(&'static str),
    #[error("No more goals inside tactic `{0}` function call.")]
    NoMoreGoalsTactic(&'static str),
    #[error("Qed failed for proof of {0} with typing error: {1}")]
    QedFailed(String,TypingError),
    #[error("Tactic `{0}` is not yet implemented")]
    UnimplementedTactic(Tactic),
    #[error("Command `{0}` is not yet implemented")]
    UnimplementedCommand(Command),
    #[error("Lambda encounter unbounded variable `{0}` on insert")]
    InsertTermUnboundedVariable(String),
}

#[derive(Error, Debug, PartialEq, Eq, Clone)]
pub enum TypingError {
    #[error("Unbound variable of depth `{0}`")]
    UnboundVariable(usize),
    #[error("Failed to typecheck `{0}` as having type `{1}`")]
    TypecheckingFail(String, String),
    #[error("Failed to unify `{0}` and `{1}`")]
    UnificationFail(String, String),
    #[error("{0} is not a subtype of {1}")]
    SubtypingFail(String, String),
    #[error("Incoherent type: {0}")]
    TypeIncoherence(String),
    #[error("Node ar position `{0}`doesn't exist, but is pointed to")]
    NodeIncorrectPointer(NodeIndex),
    #[error("constant `{0}` does not exist")]
    UndefinedConstant(String),
    #[error("tried to match a term of the non-inductive type `{0}`")]
    MatchNonInductive(String),
    #[error("a parameter of an inductive type was not ignored in a match `{0}`")]
    UnignoredInductiveParam(String),
    #[error("Match failure `{0}` against `{1}`")]
    MatchFailure(String, String),
    #[error("Invalid Elimination `{0}`")]
    InvalidElimination(String),
    #[error("worng number of arguments for an inductive type : '{0}`")]
    WrongInductiveArguments(String),
    #[error("Unknown Inductive `{0}`")]
    UnknowInductive(String),
    #[error("invalid pattern matching `{0}`")]
    InvalidPatternMatching(String),
}
