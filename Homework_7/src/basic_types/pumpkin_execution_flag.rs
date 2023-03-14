use super::{Solution, SolutionValuePair};

pub enum PumpkinExecutionFlag {
    Optimal { optimal_solution: SolutionValuePair },
    Feasible { feasible_solution: Solution },
    Infeasible,
    Timeout,
}
