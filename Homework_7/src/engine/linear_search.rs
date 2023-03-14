use crate::basic_types::{Function, SolutionValuePair, Stopwatch};

use super::ConstraintSatisfactionSolver;

// Optimise the given objective function within the csp solver. This returns the optimal solution
// for the problem instance with which the solver is initialised.
pub fn solve(
    csp_solver: &mut ConstraintSatisfactionSolver,
    objective_function: &Function,
    stopwatch: &Stopwatch,
) -> SolutionValuePair {
    todo!()
}
