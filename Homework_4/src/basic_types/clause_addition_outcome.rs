#[derive(Debug, PartialEq, Eq)]
pub enum ClauseAdditionOutcome {
    Infeasible,
    NoConflictDetected,
}
