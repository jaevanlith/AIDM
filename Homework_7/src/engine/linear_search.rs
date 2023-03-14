use crate::basic_types::{Function, PropositionalVariable, Solution, SolutionValuePair, Stopwatch};
use crate::encoders::{EncodingStatus, GeneralisedTotaliserEncoder};

use super::ConstraintSatisfactionSolver;

// Optimise the given objective function within the csp solver. This returns the optimal solution
// for the problem instance with which the solver is initialised.
pub fn solve(
    csp_solver: &mut ConstraintSatisfactionSolver,
    objective_function: &Function,
    _stopwatch: &Stopwatch,
) -> SolutionValuePair {

    // init totaliser
    let mut objective_value= u64 ::MAX;
    let mut solution;
    let mut totaliser = GeneralisedTotaliserEncoder :: new(objective_function, csp_solver);

    solution = Solution :: new(csp_solver.get_propositional_assignments(), csp_solver.get_integer_assignments());

    // search for better solutions
    let mut conflict : bool = false;
    while !conflict && csp_solver.get_state().has_solution() {

        // save the previous solution
        solution.update(csp_solver.get_propositional_assignments(), csp_solver.get_integer_assignments());
        objective_value = objective_function.evaluate_solution(&solution);

        // reset solver
        csp_solver.restore_state_at_root();

        // update k
        let status = totaliser.constrain_at_most_k(objective_value - 1, csp_solver);

        match status {
            EncodingStatus::ConflictDetected => conflict = true,
            _ => {}
        }

        csp_solver.solve(i64 :: MAX);

        //report
        if !conflict && csp_solver.get_state().has_solution() {
            println!("s FEASIBLE");
            println!("o {}", objective_value);
            println!("v {}", stringify_solution(&solution));
        }
    }
    return SolutionValuePair :: new(solution, objective_value);
}

// !! function from the main class !!
fn stringify_solution(solution: &Solution) -> String {
    (0..solution.num_propositional_variables())
        .map(|index| PropositionalVariable::new(index.try_into().unwrap()))
        .map(|var| {
            if solution[var] {
                format!("{} ", var.index())
            } else {
                format!("-{} ", var.index())
            }
        })
        .collect::<String>()
}