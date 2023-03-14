mod generalised_totaliser_encoder;

pub use generalised_totaliser_encoder::*;

/// Result of applying an encoding to the constraint solver.
#[derive(Debug, PartialEq, Eq)]
pub enum EncodingStatus {
    /// The encoding was applied without triggering any conflicts.
    NoConflictDetected,

    /// Applying the encoding detected a conflict.
    ConflictDetected,
}
