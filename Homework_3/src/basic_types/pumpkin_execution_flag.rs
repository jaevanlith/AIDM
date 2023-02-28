use super::Solution;

pub enum PumpkinExecutionFlag {
    Feasible { feasible_solution: Solution },
    Infeasible,
    Timeout,
}
