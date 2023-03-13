use crate::{basic_types::Literal, engine::ConstraintSatisfactionSolver};

use super::EncodingStatus;

pub struct TotaliserEncoder {
    // Add any fields you need here.
}

impl TotaliserEncoder {
    /// Create a new totaliser encoder for the given literals. These literals form the left-hand
    /// side for the cardinality constraint which we want to encode. The right-hand side will be
    /// given when [`TotaliserEncoder::constrain_at_most_k`] is called.
    pub fn new(_literals: Vec<Literal>) -> TotaliserEncoder {
        TotaliserEncoder {
            // Initialise your fields
        }
    }

    /// Add the constraint to the csp solver, and set the upper-bound to `k`. When called
    /// repeatidly, this method re-uses the encoding of previous calls. This only works when `k` is
    /// strictly decreasing in successive calls. Calling this method with a value `k` and then
    /// calling it again with value `k + 1` is undefined behavior.
    pub fn constrain_at_most_k(
        &mut self,
        _k: usize,
        _csp_solver: &mut ConstraintSatisfactionSolver,
    ) -> EncodingStatus {
        todo!()
    }
}
