use super::cp::CPEngineDataStructures;
use std::collections::HashSet;
use super::sat::SATEngineDataStructures;
use super::{AssignmentsInteger, AssignmentsPropositional, SATCPMediator};
use crate::arguments::ArgumentHandler;
use crate::basic_types::{
    BranchingDecision, CSPSolverExecutionFlag, ClauseAdditionOutcome, ClauseReference,
    IntegerVariable, Literal, PropagationStatusCP, PropagationStatusClausal,
    PropagationStatusOneStepCP, PropagatorIdentifier, PropositionalConjunction,
    PropositionalVariable, Stopwatch,
};

use crate::engine::{DebugHelper, DomainManager};
use crate::propagators::ConstraintProgrammingPropagator;
use crate::pumpkin_asserts::*;

pub struct ConstraintSatisfactionSolver {
    state: CSPSolverState,
    sat_data_structures: SATEngineDataStructures,
    cp_data_structures: CPEngineDataStructures,
    cp_propagators: Vec<Box<dyn ConstraintProgrammingPropagator>>,
    sat_cp_mediator: SATCPMediator,
    seen: Vec<bool>,
    counters: Counters,
    internal_parameters: ConstraintSatisfactionSolverInternalParameters,
    stopwatch: Stopwatch,
}

//methods that offer basic functionality
impl ConstraintSatisfactionSolver {
    pub fn new(argument_handler: &ArgumentHandler) -> ConstraintSatisfactionSolver {
        let mut csp_solver = ConstraintSatisfactionSolver {
            state: CSPSolverState::new(),
            sat_data_structures: SATEngineDataStructures::new(argument_handler),
            cp_data_structures: CPEngineDataStructures::new(argument_handler),
            cp_propagators: vec![],
            sat_cp_mediator: SATCPMediator::new(),
            seen: vec![],
            counters: Counters::new(
                argument_handler.get_integer_argument("num-conflicts-per-restart"),
            ),
            internal_parameters: ConstraintSatisfactionSolverInternalParameters::new(
                argument_handler,
            ),
            stopwatch: Stopwatch::new(i64::MAX),
        };

        //we introduce a dummy variable set to true at the root level
        //  this is useful for convenience when a fact needs to be expressed that is always true
        //  e.g., this makes writing propagator explanations easier for corner cases
        let root_variable = csp_solver
            .sat_cp_mediator
            .create_new_propositional_variable(&mut csp_solver.sat_data_structures);
        let true_literal = Literal::new(root_variable, true);

        csp_solver
            .sat_data_structures
            .assignments_propositional
            .true_literal = true_literal;

        csp_solver
            .sat_data_structures
            .assignments_propositional
            .false_literal = !true_literal;

        csp_solver.sat_cp_mediator.true_literal = true_literal;
        csp_solver.sat_cp_mediator.false_literal = !true_literal;

        csp_solver.add_unit_clause(true_literal);

        csp_solver
    }

    pub fn solve_under_assumptions(
        &mut self,
        assumptions: &[Literal],
        time_limit_in_seconds: i64,
    ) -> CSPSolverExecutionFlag {
        self.initialise(assumptions, time_limit_in_seconds);
        self.solve_internal()
    }

    pub fn extract_core(&mut self) -> Vec<Literal> {
        pumpkin_assert_simple!(
            self.state.is_infeasible_under_assumptions(),
            "Cannot extract core unless the solver is in the infeasible under assumption state."
        );
        todo!();
    }

    pub fn solve(&mut self, time_limit_in_seconds: i64) -> CSPSolverExecutionFlag {
        let dummy_assumptions: Vec<Literal> = vec![];
        self.solve_under_assumptions(&dummy_assumptions, time_limit_in_seconds)
    }

    pub fn reset_variable_selection(&mut self, random_seed: i64) {
        pumpkin_assert_simple!(self.state.is_ready());
        self.sat_data_structures
            .propositional_variable_selector
            .reset(random_seed);
    }

    pub fn get_state(&self) -> &CSPSolverState {
        &self.state
    }

    pub fn create_new_propositional_variable(&mut self) -> PropositionalVariable {
        self.sat_cp_mediator
            .create_new_propositional_variable(&mut self.sat_data_structures)
    }

    pub fn create_new_integer_variable(
        &mut self,
        lower_bound: i32,
        upper_bound: i32,
    ) -> IntegerVariable {
        self.sat_cp_mediator.create_new_integer_variable(
            lower_bound,
            upper_bound,
            &mut self.sat_data_structures,
            &mut self.cp_data_structures,
        )
    }

    pub fn get_propositional_assignments(&self) -> &AssignmentsPropositional {
        &self.sat_data_structures.assignments_propositional
    }

    pub fn get_lower_bound_literal(
        &self,
        integer_variable: IntegerVariable,
        lower_bound: i32,
    ) -> Literal {
        self.sat_cp_mediator
            .get_lower_bound_literal(integer_variable, lower_bound)
    }

    pub fn get_integer_assignments(&self) -> &AssignmentsInteger {
        &self.cp_data_structures.assignments_integer
    }

    pub fn set_solution_guided_search(&mut self) {
        pumpkin_assert_simple!(
            self.state.has_solution(),
            "Cannot set solution guided search without a solution in the solver."
        );

        for variable in self
            .sat_data_structures
            .assignments_propositional
            .get_propositional_variables()
        {
            //variable values get assigned the value as in the current assignment
            //note: variables created after calling this method may follow a different strategy
            let new_truth_value = self
                .sat_data_structures
                .assignments_propositional
                .is_variable_assigned_true(variable);

            self.sat_data_structures
                .propositional_value_selector
                .update_and_freeze(variable, new_truth_value);
        }
    }

    pub fn set_fixed_phases_for_variables(&mut self, literals: &[Literal]) {
        for literal in literals {
            self.sat_data_structures
                .propositional_value_selector
                .update_and_freeze(literal.get_propositional_variable(), literal.is_positive());
        }
    }

    pub fn restore_state_at_root(&mut self) {
        pumpkin_assert_simple!(self.state.has_solution() && self.get_decision_level() > 0);

        self.backtrack(0);
        self.state.declare_ready();
    }
}

//methods that serve as the main building blocks
impl ConstraintSatisfactionSolver {
    fn initialise(&mut self, assumptions: &[Literal], time_limit_in_seconds: i64) {
        let num_propositional_variables = self
            .sat_data_structures
            .assignments_propositional
            .num_propositional_variables() as usize;

        self.state.declare_solving();
        self.stopwatch.reset(time_limit_in_seconds);
        self.sat_data_structures.assumptions = assumptions.to_owned();
        self.seen.resize(num_propositional_variables, false);

        self.counters.num_conflicts_until_restart =
            self.internal_parameters.num_conflicts_per_restart as i64;
    }

    fn solve_internal(&mut self) -> CSPSolverExecutionFlag {
        loop {
            if self.stopwatch.get_remaining_time_budget() <= 0 {
                self.state.declare_timeout();
                return CSPSolverExecutionFlag::Timeout;
            }

            self.propagate_enqueued();

            if self.state.no_conflict() {
                if self.should_restart() {
                    self.backtrack(0);
                }

                self.sat_data_structures
                    .assignments_propositional
                    .increase_decision_level();
                self.cp_data_structures
                    .assignments_integer
                    .increase_decision_level();

                match self.sat_data_structures.get_next_branching_decision() {
                    Some(branching_decision) => match branching_decision {
                        BranchingDecision::Assumption { assumption_literal } => {
                            //Case 1: the assumption is unassigned, assign it
                            if self
                                .sat_data_structures
                                .assignments_propositional
                                .is_literal_unassigned(assumption_literal)
                            {
                                self.sat_data_structures
                                    .assignments_propositional
                                    .enqueue_decision_literal(assumption_literal);
                            //Case 2: the assumption has already been set to true
                            //  this happens when other assumptions propagated the literal
                            //  or the assumption is already set to true at the root level
                            } else if self
                                .sat_data_structures
                                .assignments_propositional
                                .is_literal_assigned_true(assumption_literal)
                            {
                                //in this case, do nothing
                                //  note that the solver will then increase the decision level without enqueuing a decision literal
                                //  this is necessary because by convention the solver will try to assign the i-th assumption literal at decision level i+1
                            }
                            //Case 3: the assumption literal is in conflict with the input assumption
                            //  which means the instance is infeasible under the current assumptions
                            else {
                                pumpkin_assert_moderate!(
                                    self.sat_data_structures
                                        .assignments_propositional
                                        .get_literal_assignment_level(assumption_literal)
                                        == 0
                                        || self
                                            .sat_data_structures
                                            .assignments_propositional
                                            .is_literal_propagated(assumption_literal),
                                );

                                self.state
                                    .declare_infeasible_under_assumptions(assumption_literal);
                                return CSPSolverExecutionFlag::InfeasibleUnderAssumptions;
                            }
                        }
                        BranchingDecision::StandardDecision { decision_literal } => {
                            self.counters.num_decisions += 1;
                            self.sat_data_structures
                                .assignments_propositional
                                .enqueue_decision_literal(decision_literal);
                        }
                    },
                    None => {
                        self.state.declare_solution_found();
                        return CSPSolverExecutionFlag::Feasible;
                    }
                }
            } else {
                if self
                    .sat_data_structures
                    .assignments_propositional
                    .is_at_the_root_level()
                {
                    self.state.declare_infeasible();
                    return CSPSolverExecutionFlag::Infeasible;
                }

                let conflict_reference = self.get_conflict_clause();
                let analysis_result = self.analyse_conflict(conflict_reference);
                self.counters.num_unit_clauses_learned +=
                    (analysis_result.learned_literals.len() == 1) as u64;
                self.process_conflict_analysis_result(analysis_result);

                self.state.declare_solving();

                self.sat_data_structures.decay_clause_activities();
                self.sat_data_structures
                    .propositional_variable_selector
                    .decay_activities();
            }
        }
    }

    //changes the state based on the conflict analysis result given as input
    //i.e., adds the learned clause to the database, backtracks, enqueues the propagated literal, and updates internal data structures for simple moving averages
    //note that no propagation is done, this is left to the solver
    fn process_conflict_analysis_result(&mut self, analysis_result: ConflictAnalysisResult) {
        //unit clauses are treated in a special way: they are added as decision literals at decision level 0
        if analysis_result.learned_literals.len() == 1 {
            self.backtrack(0);
            let unit_clause = analysis_result.learned_literals[0];
            pumpkin_assert_simple!(
                self.sat_data_structures
                    .assignments_propositional
                    .is_literal_unassigned(unit_clause),
                "Do not expect to learn a literal that is already set."
            );

            self.sat_data_structures
                .assignments_propositional
                .enqueue_decision_literal(unit_clause);
            //state_.UpdateMovingAveragesForRestarts(1);
        } else {
            //int lbd = state_.ComputeLBD(&analysis_result_.learned_clause_literals[0] + 1, analysis_result_.learned_clause_literals.size() - 1);
            //state_.UpdateMovingAveragesForRestarts(lbd);

            self.backtrack(analysis_result.backjump_level);

            let propagated_literal = analysis_result.learned_literals[0];

            let learned_clause_reference = self
                .sat_data_structures
                .add_clause_unchecked(analysis_result.learned_literals, true);

            self.sat_data_structures
                .assignments_propositional
                .enqueue_propagated_literal(propagated_literal, learned_clause_reference.id);
        }
    }

    fn get_conflict_clause(&mut self) -> ClauseReference {
        pumpkin_assert_simple!(self.state.conflict_detected());
        if self.state.is_clausal_conflict() {
            self.state.get_conflict_clause_reference()
        } else {
            let failure_literals = self
                .state
                .get_conflict_reason_cp()
                .clone()
                .into_iter()
                .map(|p| !self.sat_cp_mediator.get_predicate_literal(p))
                .collect();

            self.sat_data_structures
                .add_explanation_clause_unchecked(failure_literals)
        }
    }

    fn should_restart(&self) -> bool {
        pumpkin_assert_moderate!(
            self.counters.num_conflicts_until_restart > 0 || self.get_decision_level() > 0
        );
        self.counters.num_conflicts_until_restart <= 0
    }

    fn is_conflict_clause_set(&self) -> bool {
        true
    }

    fn backtrack(&mut self, backtrack_level: u32) {
        pumpkin_assert_simple!(backtrack_level < self.get_decision_level());

        self.sat_data_structures.backtrack(backtrack_level);
        self.cp_data_structures.backtrack(backtrack_level);
        //  note that sat_cp_mediator sync should be called after the sat/cp data structures backtrack
        self.sat_cp_mediator.synchronise(
            &self.sat_data_structures.assignments_propositional,
            &self.cp_data_structures.assignments_integer,
        );
        //for now all propagators are called to synchronise
        //  in the future this will be improved in two ways:
        //      allow incremental synchronisation
        //      only call the subset of propagators that were notified since last backtrack
        for propagator_id in 0..self.cp_propagators.len() {
            let domains = DomainManager::new(
                propagator_id,
                &mut self.cp_data_structures.assignments_integer,
            );
            self.cp_propagators[propagator_id].synchronise(&domains);
        }

        if backtrack_level == 0 {
            self.sat_data_structures
                .shrink_learned_clause_database_if_needed();

            self.counters.num_conflicts_until_restart =
                self.internal_parameters.num_conflicts_per_restart as i64;

            self.counters.num_restarts += 1;
        }
    }

    // fn all_assigned(&mut self, w_x: &Vec<Literal>) -> bool {
    //     // all assigned?
    //     for i in w_x {
    //         if self.sat_data_structures.assignments_propositional.is_variable_unassigned(i.get_propositional_variable()) {
    //             return false
    //         }
    //     }
    //     return true
    // }

    fn analyse_conflict(&mut self, conflict_reference: ClauseReference) -> ConflictAnalysisResult {
        let decision_lev = self.sat_data_structures.assignments_propositional.get_decision_level();
        let mut w_l = self.sat_data_structures.clause_allocator.get_mutable_clause(conflict_reference).get_literal_slice().clone().to_vec();
        let mut stack = self.sat_data_structures.assignments_propositional.trail.clone();

        loop {
            let mut x_i = stack.pop().unwrap(); // stack
            // println!("{:?}", x_i);

            if w_l.contains(&!x_i) {

            } else if w_l.contains(&x_i) {
                x_i = !x_i
            } else {
                continue
            }

            let mut prev_clause = ClauseReference {
                id: conflict_reference.id as u32 - 1,
            };

            let mut w_x = self.sat_data_structures.clause_allocator.get_mutable_clause(prev_clause).get_literal_slice().clone().to_vec();
            // println!("w_x: {:?}", w_x);
            while !w_x.contains(&x_i)  { // assume linear consideration of clauses
                prev_clause = ClauseReference {
                    id: prev_clause.id as u32 - 1,
                };
                w_x = self.sat_data_structures.clause_allocator.get_mutable_clause(prev_clause).get_literal_slice().clone().to_vec();
                // println!("w_x: {:?}", w_x);
            }

            w_l.retain(|&x| x != x_i && x != !x_i);
            w_x.retain(|&x| x != x_i && x != !x_i);
            w_l.extend(&w_x);
            let mut seen = HashSet::new();
            w_l.retain(|&c| {
                let is_first = !seen.contains(&c);
                seen.insert(c);
                is_first
            });

            let mut count : u32 = 0;
            let mut lev_prop : u32 = 0;
            for i in &w_l {
                if self.sat_data_structures.assignments_propositional.is_variable_unassigned(i.get_propositional_variable()) ||
                    decision_lev == self.sat_data_structures.assignments_propositional.get_variable_assignment_level(i.get_propositional_variable()) {
                    count = count + 1;
                } else {
                    lev_prop = std::cmp::max(lev_prop, self.sat_data_structures.assignments_propositional.get_variable_assignment_level(i.get_propositional_variable()))
                }
            }
            // println!("disjoint: {:?}", count);
            // println!("w_l: {:?}", lev_prop);

            stack.push(x_i);

            if count  == 1  {
                return ConflictAnalysisResult {
                    learned_literals: w_l,
                    backjump_level: lev_prop as u32,
                }
            }
        }
    }

    fn propagate_enqueued(&mut self) {
        let num_assigned_variables_old = self
            .sat_data_structures
            .assignments_propositional
            .num_assigned_propositional_variables();

        loop {
            self.sat_cp_mediator
                .synchronise_propositional_trail_based_on_integer_trail(
                    &mut self.sat_data_structures.assignments_propositional,
                    &self.cp_data_structures.assignments_integer,
                );

            let propagation_status_clausal = self.sat_data_structures.propagate_clauses();

            if let PropagationStatusClausal::ConflictDetected { reason_code } =
                propagation_status_clausal
            {
                self.state
                    .declare_clausal_conflict(ClauseReference { id: reason_code });
                break;
            }

            self.sat_cp_mediator
                .synchronise_integer_trail_based_on_propositional_trail(
                    &self.sat_data_structures.assignments_propositional,
                    &mut self.cp_data_structures,
                    &mut self.cp_propagators,
                );

            //propagate boolean propagators - todo add these special-case propagators

            //propagate (conventional) CP propagators
            let propagation_status_one_step_cp = self.propagate_cp_one_step();

            match propagation_status_one_step_cp {
                PropagationStatusOneStepCP::ConflictDetected {
                    failure_reason: conflict_reason,
                } => {
                    self.sat_cp_mediator
                        .synchronise_propositional_trail_based_on_integer_trail(
                            &mut self.sat_data_structures.assignments_propositional,
                            &self.cp_data_structures.assignments_integer,
                        );

                    self.state.declare_cp_conflict(conflict_reason);
                    break;
                }
                PropagationStatusOneStepCP::PropagationHappened => {
                    //do nothing, the result will be that the clausal propagator will go next
                    //  recall that the idea is to always propagate simpler propagators before more complex ones
                    //  after a cp propagation was done one step, it is time to go to the clausal propagator
                }
                PropagationStatusOneStepCP::FixedPoint => {
                    break;
                }
            } //end match
        }

        self.counters.num_conflicts += self.state.conflict_detected() as u64;
        self.counters.num_conflicts_until_restart -= self.state.conflict_detected() as i64;

        self.counters.num_propagations +=
            self.sat_data_structures
                .assignments_propositional
                .num_assigned_propositional_variables() as u64
                - num_assigned_variables_old as u64;

        //Only check fixed point propagation if there was no reported conflict.
        pumpkin_assert_extreme!(
            self.state.conflict_detected()
                || DebugHelper::debug_fixed_point_propagation(
                    &self.cp_data_structures.assignments_integer,
                    &self.sat_data_structures,
                    &self.cp_propagators,
                )
        );
    }

    fn propagate_cp_one_step(&mut self) -> PropagationStatusOneStepCP {
        while !self.cp_data_structures.propagator_queue.is_empty() {
            let num_predicates_on_trail_before = self
                .cp_data_structures
                .assignments_integer
                .num_trail_entries();
            let propagator_identifier = self.cp_data_structures.propagator_queue.pop();
            let propagator = &mut self.cp_propagators[propagator_identifier.id as usize];
            let mut domains = DomainManager::new(
                propagator_identifier.id as usize,
                &mut self.cp_data_structures.assignments_integer,
            );

            let propagation_status_cp = propagator.propagate(&mut domains);

            match propagation_status_cp {
                //if there was a conflict, then stop any further propagation and proceed to conflict analysis
                PropagationStatusCP::ConflictDetected { failure_reason } => {
                    pumpkin_assert_advanced!(DebugHelper::debug_reported_failure(
                        &self.cp_data_structures.assignments_integer,
                        &failure_reason,
                        propagator.as_ref(),
                        propagator_identifier,
                    ));

                    return PropagationStatusOneStepCP::ConflictDetected { failure_reason };
                }
                PropagationStatusCP::NoConflictDetected => {
                    //if at least one integer domain change was made, stop further propagation
                    //  the point is to go to the clausal propagator before continuing with other propagators
                    let num_propagations_done = self
                        .cp_data_structures
                        .assignments_integer
                        .num_trail_entries()
                        - num_predicates_on_trail_before;

                    if num_propagations_done > 0 {
                        //notify other propagators
                        //  note that during propagators, predicates are placed on the assignment_integer trail
                        //      but no notifying is done for propagators
                        //  this is because the propagator does not have all the info on which propagators to notify when propagating
                        //here we do the notification by removing the predicates from the trail, and apply them in the same order
                        //  but this time notify all propagators of the relevant changes
                        //  note that even the propagator that did the changes needs to be notified
                        //  since propagators are not required to propagate until a fixed point in one step

                        //the current solution of copying from the trail, popping, and reapplying is not ideal
                        //  todo think about better ways
                        let propagations = self
                            .cp_data_structures
                            .assignments_integer
                            .get_last_predicates_on_trail(num_propagations_done);
                        self.cp_data_structures
                            .assignments_integer
                            .undo_trail(num_propagations_done);

                        for predicate in propagations {
                            self.cp_data_structures.apply_predicate(
                                &predicate,
                                Some(propagator_identifier),
                                &mut self.cp_propagators,
                            );
                        }

                        return PropagationStatusOneStepCP::PropagationHappened;
                    }
                }
            }
        }
        PropagationStatusOneStepCP::FixedPoint
    }
}

//methods for adding constraints (propagators and clauses)
impl ConstraintSatisfactionSolver {
    pub fn add_propagator(&mut self, propagator_to_add: Box<dyn ConstraintProgrammingPropagator>) {
        pumpkin_assert_simple!(propagator_to_add.priority() <= 3, "The propagator priority exceeds 3. Currently we only support values up to 3, but this can easily be changed if there is a good reason.");

        self.sat_data_structures
            .clause_allocator
            .reduce_id_limit_by_one();

        let new_propagator_id = PropagatorIdentifier {
            id: self.cp_propagators.len() as u32,
        };
        self.cp_propagators.push(propagator_to_add);

        let new_propagator = &mut self.cp_propagators[new_propagator_id.id as usize];
        let mut domains = DomainManager::new(
            new_propagator_id.id as usize,
            &mut self.cp_data_structures.assignments_integer,
        );

        self.cp_data_structures
            .watch_list_cp
            .add_watches_for_propagator(new_propagator.as_ref(), new_propagator_id);

        new_propagator.initialise_at_root(&mut domains);

        let root_status = new_propagator.initialise_at_root(&mut domains);

        pumpkin_assert_simple!(root_status.no_conflict(), "For now we crash when adding a new propagator that detects a conflict at the root node, even though this is not necessarily an error. Should handle better in the future.");

        self.propagate_enqueued();
        pumpkin_assert_simple!(self.state.no_conflict(), "Root conflict detected after adding propagator, for now we crash the program but this may not necessarily be an error.");
    }

    pub fn add_permanent_clause(&mut self, literals: Vec<Literal>) -> ClauseAdditionOutcome {
        self.sat_data_structures.add_permanent_clause(literals)
    }

    pub fn add_permanent_implication_unchecked(&mut self, lhs: Literal, rhs: Literal) {
        self.sat_data_structures
            .add_permanent_implication_unchecked(lhs, rhs);
    }

    pub fn add_permanent_ternary_clause_unchecked(&mut self, a: Literal, b: Literal, c: Literal) {
        self.sat_data_structures
            .add_permanent_ternary_clause_unchecked(a, b, c);
    }

    pub fn add_unit_clause(&mut self, unit_clause: Literal) -> ClauseAdditionOutcome {
        pumpkin_assert_simple!(self.get_decision_level() == 0);
        pumpkin_assert_simple!(self.is_propagation_complete());

        //if the literal representing the unit clause is unassigned, assign it
        if self
            .sat_data_structures
            .assignments_propositional
            .is_literal_unassigned(unit_clause)
        {
            self.sat_data_structures
                .assignments_propositional
                .enqueue_decision_literal(unit_clause);

            self.propagate_enqueued();

            if self.state.conflict_detected() {
                ClauseAdditionOutcome::Infeasible
            } else {
                ClauseAdditionOutcome::NoConflictDetected
            }
        }
        //the unit clause is already present, no need to do anything
        else if self
            .sat_data_structures
            .assignments_propositional
            .is_literal_assigned_true(unit_clause)
        {
            ClauseAdditionOutcome::NoConflictDetected
        }
        //the unit clause is falsified at the root level
        else {
            ClauseAdditionOutcome::Infeasible
        }
    }
}

//methods for getting simple info out of the solver
impl ConstraintSatisfactionSolver {
    pub fn is_propagation_complete(&self) -> bool {
        self.sat_data_structures
            .is_clausal_propagation_at_fixed_point()
            && self.cp_data_structures.propagator_queue.is_empty()
    }

    fn get_decision_level(&self) -> u32 {
        pumpkin_assert_moderate!(
            self.sat_data_structures
                .assignments_propositional
                .get_decision_level()
                == self
                    .cp_data_structures
                    .assignments_integer
                    .get_decision_level()
        );
        self.sat_data_structures
            .assignments_propositional
            .get_decision_level()
    }
}

struct Counters {
    pub num_decisions: u64,
    pub num_conflicts: u64,
    pub num_propagations: u64,
    pub num_unit_clauses_learned: u64,
    pub num_conflicts_until_restart: i64, //in case the solver gets into a chain of conflicts, this value could go get negative
    pub num_restarts: u64,
}

impl Counters {
    fn new(num_conflicts_until_restart: i64) -> Counters {
        Counters {
            num_decisions: 0,
            num_conflicts: 0,
            num_propagations: 0,
            num_unit_clauses_learned: 0,
            num_conflicts_until_restart,
            num_restarts: 0,
        }
    }
}

pub struct ConflictAnalysisResult {
    pub learned_literals: Vec<Literal>,
    pub backjump_level: u32,
}

#[derive(Default)]
enum CSPSolverStateInternal {
    #[default]
    Ready,
    Solving,
    ContainsSolution,
    ConflictClausal {
        conflict_clause_reference: ClauseReference,
    },
    ConflictCP {
        conflict_reason: PropositionalConjunction,
    },
    Infeasible,
    InfeasibleUnderAssumptions {
        violated_assumption: Literal,
    },
    Timeout,
}

pub struct CSPSolverState {
    internal_state: CSPSolverStateInternal,
}

impl CSPSolverState {
    pub fn new() -> CSPSolverState {
        CSPSolverState {
            internal_state: CSPSolverStateInternal::Ready,
        }
    }

    pub fn is_ready(&self) -> bool {
        matches!(self.internal_state, CSPSolverStateInternal::Ready)
    }

    pub fn no_conflict(&self) -> bool {
        !self.conflict_detected()
    }

    pub fn conflict_detected(&self) -> bool {
        self.is_clausal_conflict() || self.is_cp_conflict()
    }

    pub fn is_clausal_conflict(&self) -> bool {
        matches!(
            self.internal_state,
            CSPSolverStateInternal::ConflictClausal {
                conflict_clause_reference: _
            }
        )
    }

    pub fn is_cp_conflict(&self) -> bool {
        matches!(
            self.internal_state,
            CSPSolverStateInternal::ConflictCP { conflict_reason: _ }
        )
    }

    pub fn is_infeasible_under_assumptions(&self) -> bool {
        matches!(
            self.internal_state,
            CSPSolverStateInternal::InfeasibleUnderAssumptions {
                violated_assumption: _
            }
        )
    }

    pub fn get_violated_assumption(&self) -> Literal {
        if let CSPSolverStateInternal::InfeasibleUnderAssumptions {
            violated_assumption,
        } = self.internal_state
        {
            violated_assumption
        } else {
            panic!("Cannot extract violated assumption without getting the solver into the infeasible under assumptions state.");
        }
    }

    pub fn get_conflict_clause_reference(&self) -> ClauseReference {
        if let CSPSolverStateInternal::ConflictClausal {
            conflict_clause_reference,
        } = self.internal_state
        {
            conflict_clause_reference
        } else {
            panic!("Cannot extract conflict clause if solver is not in a clausal conflict.");
        }
    }

    pub fn get_conflict_reason_cp(&self) -> &PropositionalConjunction {
        if let CSPSolverStateInternal::ConflictCP { conflict_reason } = &self.internal_state {
            conflict_reason
        } else {
            panic!("Cannot extract conflict reason of a cp propagator if solver is not in a cp conflict.");
        }
    }

    pub fn timeout(&self) -> bool {
        matches!(self.internal_state, CSPSolverStateInternal::Timeout)
    }

    pub fn has_solution(&self) -> bool {
        matches!(
            self.internal_state,
            CSPSolverStateInternal::ContainsSolution
        )
    }

    fn declare_ready(&mut self) {
        pumpkin_assert_simple!(self.has_solution());
        self.internal_state = CSPSolverStateInternal::Ready;
    }

    fn declare_solving(&mut self) {
        pumpkin_assert_simple!(self.is_ready() || self.conflict_detected());
        self.internal_state = CSPSolverStateInternal::Solving;
    }

    fn declare_infeasible(&mut self) {
        self.internal_state = CSPSolverStateInternal::Infeasible;
    }

    fn declare_clausal_conflict(&mut self, failure_reference: ClauseReference) {
        self.internal_state = CSPSolverStateInternal::ConflictClausal {
            conflict_clause_reference: failure_reference,
        };
    }

    fn declare_cp_conflict(&mut self, failure_reason: PropositionalConjunction) {
        self.internal_state = CSPSolverStateInternal::ConflictCP {
            conflict_reason: failure_reason,
        };
    }

    fn declare_solution_found(&mut self) {
        self.internal_state = CSPSolverStateInternal::ContainsSolution;
    }

    fn declare_timeout(&mut self) {
        self.internal_state = CSPSolverStateInternal::Timeout;
    }

    fn declare_infeasible_under_assumptions(&mut self, violated_assumption: Literal) {
        self.internal_state = CSPSolverStateInternal::InfeasibleUnderAssumptions {
            violated_assumption,
        }
    }
}

pub struct ConstraintSatisfactionSolverInternalParameters {
    pub num_conflicts_per_restart: u64,
}

impl ConstraintSatisfactionSolverInternalParameters {
    pub fn new(
        argument_handler: &ArgumentHandler,
    ) -> ConstraintSatisfactionSolverInternalParameters {
        ConstraintSatisfactionSolverInternalParameters {
            num_conflicts_per_restart: argument_handler
                .get_integer_argument("num-conflicts-per-restart")
                as u64,
        }
    }
}

#[cfg(test)]
mod tests {
    use std::collections::HashSet;

    use super::*;
    use crate::Pumpkin;

    /// Courtesy of:
    /// https://www.cs.princeton.edu/courses/archive/fall13/cos402/readings/SAT_learning_clauses.pdf
    #[test]
    fn analyse_conflict_performs_first_uip_learning() {
        let argument_handler = Pumpkin::create_argument_handler();
        let mut solver = ConstraintSatisfactionSolver::new(&argument_handler);

        let x = std::iter::from_fn(|| Some(solver.create_new_propositional_variable()))
            .map(|var| Literal::new(var, true))
            .take(9)
            .collect::<Vec<_>>();

        solver.add_permanent_clause(vec![x[0], x[1]]);
        solver.add_permanent_clause(vec![x[0], x[2], x[6]]);
        solver.add_permanent_clause(vec![!x[1], !x[2], x[3]]);
        solver.add_permanent_clause(vec![!x[3], x[4], x[7]]);
        solver.add_permanent_clause(vec![!x[3], x[5], x[8]]);
        solver.add_permanent_clause(vec![!x[4], !x[5]]);

        solver.initialise(&[], i64::MAX);

        enqueue_and_propagate(&mut solver, !x[6]);
        enqueue_and_propagate(&mut solver, !x[7]);
        enqueue_and_propagate(&mut solver, !x[8]);
        enqueue_and_propagate(&mut solver, !x[0]);

        assert!(solver.state.conflict_detected());

        let result = solver.analyse_conflict(solver.state.get_conflict_clause_reference());
        let learnt_lits: HashSet<Literal> = result.learned_literals.into_iter().collect();
        let expected_lits: HashSet<Literal> = [!x[3], x[7], x[8]].into_iter().collect();

        println!("{:?}", learnt_lits);

        assert_eq!(learnt_lits, expected_lits);
        assert_eq!(result.backjump_level, 3);
    }

    fn enqueue_and_propagate(solver: &mut ConstraintSatisfactionSolver, lit: Literal) {
        solver
            .sat_data_structures
            .assignments_propositional
            .increase_decision_level();

        solver
            .sat_data_structures
            .assignments_propositional
            .enqueue_decision_literal(lit);

        solver.propagate_enqueued();
    }
}
