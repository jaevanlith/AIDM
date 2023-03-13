mod totaliser_encoder;

pub use totaliser_encoder::*;

use crate::basic_types::ClauseAdditionOutcome;

/// Result of applying an encoding to the constraint solver.
#[derive(Debug, PartialEq, Eq)]
pub enum EncodingStatus {
    /// The encoding was applied without triggering any conflicts.
    Success,

    /// Applying the encoding detected a conflict.
    Conflict,
}

impl From<ClauseAdditionOutcome> for EncodingStatus {
    fn from(value: ClauseAdditionOutcome) -> Self {
        match value {
            ClauseAdditionOutcome::Infeasible => EncodingStatus::Conflict,
            ClauseAdditionOutcome::NoConflictDetected => EncodingStatus::Success,
        }
    }
}
