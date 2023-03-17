use crate::{
    basic_types::{
        EnqueueStatus, IntegerVariable, Predicate, PropagationStatusCP, PropositionalConjunction,
    },
    engine::DomainManager,
};
use crate::engine::DomainOperationOutcome;

use super::ConstraintProgrammingPropagator;

/// Propagator for the constraint \sum w_i * x_i >= c.
///
/// Note: Even though the domains of integer variables are represented as signed integers, expect
/// them to be unsigned values. Calling the propagator with variables which have negative bounds on
/// their domains can be considered undefined behaviour.
pub struct LinearInequalityPropagator {
    weights : Vec<i64>,
    variables : Vec<IntegerVariable>,
    watchlist_ub: Vec<IntegerVariable>,
    watchlist_lb: Vec<IntegerVariable>,
    c : i64,
    slack: i64,
    initialised : bool,
    initial_bounds: Vec<i64>,
    explanation: Vec<Predicate>,
    opp_bounds: Vec<i64>
}

impl LinearInequalityPropagator {
    pub fn new(
        weights: Vec<i64>,
        variables: Vec<IntegerVariable>,
        c: i64,
    ) -> LinearInequalityPropagator {
        assert_eq!(weights.len(), variables.len(), 
            "Expect the number of weights to match the number of variables for the linear inequality propagator.");

        // init watchlist
        let mut watchlist_lb = Vec :: new();
        let mut watchlist_ub = Vec :: new();
        for i in 0..variables.len() {
            assert_ne!(weights[i], 0);

            if weights[i] < 0 {
                watchlist_lb.push(variables[i]);
            } else {
                watchlist_ub.push(variables[i]);
            }
        }

        LinearInequalityPropagator {
            weights,
            variables,
            watchlist_ub,
            watchlist_lb,
            c,
            slack: 0,
            initialised : false,
            initial_bounds : Vec :: new(),
            explanation : Vec :: new(),
            opp_bounds : Vec :: new(),
        }
    }

    fn create_explanation(
        &self,
        predicate: Option<Predicate>
        // Any required parameters
    ) -> PropositionalConjunction {
        let mut res = PropositionalConjunction :: new();

        for i in 0..self.variables.len() {
            let mut sum = 0;
            for j in 0..self.variables.len() {
                if predicate.is_some() && predicate.unwrap().get_integer_variable() == self.variables[j] {
                    sum += self.weights[j] * self.opp_bounds[j];
                } else if i == j {
                    sum += self.weights[j] * self.initial_bounds[j];
                } else {
                    sum += self.weights[j] * self.explanation[j].get_right_hand_side() as i64;
                }
            }

            if sum >= self.c && (predicate.is_none() || predicate.unwrap() != self.explanation[i]) {
                res.and(self.explanation[i]);
            }
        }

        return res;
    }

    fn update_bounds(&mut self, domains: &mut DomainManager) {
        for i in 0..self.variables.len() {
            if self.weights[i] < 0 {
                self.explanation[i] = domains.get_lower_bound_predicate(self.variables[i]);
            } else {
                self.explanation[i] = domains.get_upper_bound_predicate(self.variables[i]);
            }
        }
    }
}

// helper function
fn calculate_slack(c: i64, weights: Vec<i64>, variables:  Vec<IntegerVariable>, domains: &mut DomainManager) -> i64 {
    let mut slack_ub = 0;
    let mut slack_lb = 0;
    for i in 0..variables.len() {
        if weights[i] < 0 {
            slack_lb += domains.get_lower_bound(variables[i]) as i64 * weights[i];
        } else {
            slack_ub += domains.get_upper_bound(variables[i]) as i64 * weights[i];
        }
    }

    return slack_lb + slack_ub - c;
}

impl ConstraintProgrammingPropagator for LinearInequalityPropagator {
    fn propagate(&mut self, domains: &mut DomainManager) -> PropagationStatusCP {
        if !self.initialised {
            let init_status = self.initialise_at_root(domains);
            match init_status {
                PropagationStatusCP::ConflictDetected {..} => return init_status,
                _ => PropagationStatusCP::NoConflictDetected,
            };
        }

        // update slack
        self.slack = calculate_slack(self.c, self.weights.clone(), self.variables.clone(), domains);
        self.update_bounds(domains);

        // update lower bounds
        for i in 0..self.variables.len() {
            // when already assigned, no propagation needed
            if domains.is_integer_variable_assigned(self.variables[i]) { continue; }

            let mut lb = domains.get_lower_bound(self.variables[i]) as i64;
            let mut ub= domains.get_upper_bound(self.variables[i]) as i64;

            if self.weights[i] < 0 {
                let temp = ub;
                ub = lb;
                lb = temp
            }

            // validate if any update can be applied
            let diff = self.slack + (lb - ub) * self.weights[i];
            let x_minsat = ((-1 * diff) + i64::abs(self.weights[i]) - 1) / self.weights[i];
            if diff < 0 {
                let outcome;
                if self.weights[i] < 0 {
                    outcome = domains.tighten_upper_bound(self.variables[i], lb as i32 + x_minsat as i32 );
                } else {
                    outcome = domains.tighten_lower_bound(self.variables[i],  lb as i32 + x_minsat as i32);
                }

                // report
                if lb + x_minsat < 0 {
                    return PropagationStatusCP::ConflictDetected {
                        failure_reason : self.create_explanation(None),
                    }
                }

                match outcome {
                    DomainOperationOutcome::Failure => return PropagationStatusCP::ConflictDetected {
                        failure_reason : self.create_explanation(None),
                    },
                    _ => PropagationStatusCP::NoConflictDetected,
                };
            }
        }
        return PropagationStatusCP::NoConflictDetected;
    }

    fn synchronise(&mut self, _domains: &DomainManager) {
        // Left blank, it is not necessary to use this. However, if you want to, you can.
    }

    fn notify_lower_bound_integer_variable_change(
        &mut self,
        integer_variable: IntegerVariable,
        old_lower_bound: i32,
        new_lower_bound: i32,
        _domains: &DomainManager,
    ) -> EnqueueStatus {

        // get weight
        let index = self.variables.iter().position(|n| n.id == integer_variable.id).unwrap();
        let weight = self.weights[index];

        assert!(weight < 0 as i64);

        // update slack
        self.slack += (new_lower_bound as i64 - old_lower_bound as i64) * weight;

        return EnqueueStatus::ShouldEnqueue;
    }

    fn notify_upper_bound_integer_variable_change(
        &mut self,
        integer_variable: IntegerVariable,
        old_upper_bound: i32,
        new_upper_bound: i32,
        _domains: &DomainManager,
    ) -> EnqueueStatus {

        // get weight
        let index = self.variables.iter().position(|n| n.id == integer_variable.id).unwrap();
        let weight = self.weights[index];

        assert!(weight > 0 as i64);

        // update slack
        self.slack += (new_upper_bound as i64 - old_upper_bound as i64) * weight;

        return EnqueueStatus::ShouldEnqueue;
    }

    fn notify_domain_hole_integer_variable_change(
        &mut self,
        _integer_variable: IntegerVariable,
        _removed_value_from_domain: i32,
        _domains: &DomainManager,
    ) -> EnqueueStatus {
        return EnqueueStatus::DoNotEnqueue;
    }

    fn get_reason_for_propagation(&mut self, predicate: Predicate) -> PropositionalConjunction {
        return self.create_explanation(Some(predicate));
    }

    fn priority(&self) -> u32 {
        0
    }

    fn name(&self) -> &str {
        "linear programming propagator"
    }

    fn get_integer_variables_to_watch_for_lower_bound_changes(&self) -> Vec<IntegerVariable> {
        return self.watchlist_lb.clone();
    }

    fn get_integer_variables_to_watch_for_upper_bound_changes(&self) -> Vec<IntegerVariable> {
        return self.watchlist_ub.clone();
    }

    fn get_integer_variables_to_watch_for_domain_hole_changes(&self) -> Vec<IntegerVariable> {
        return Vec :: new();
    }

    fn initialise_at_root(&mut self, domains: &mut DomainManager) -> PropagationStatusCP {

        // init slack
        let mut slack_ub = 0;
        let mut slack_lb = 0;
        for i in 0..self.variables.len() {
            if self.weights[i] < 0 {
                let lb = domains.get_lower_bound(self.variables[i]) as i64;
                slack_lb += lb * self.weights[i];
                self.initial_bounds.push(lb);
                self.opp_bounds.push(domains.get_upper_bound(self.variables[i]) as i64);
                self.explanation.push(domains.get_lower_bound_predicate(self.variables[i]));
            } else {
                let ub = domains.get_upper_bound(self.variables[i]) as i64;
                slack_ub += ub * self.weights[i];
                self.initial_bounds.push(ub);
                self.opp_bounds.push(domains.get_lower_bound(self.variables[i]) as i64);
                self.explanation.push(domains.get_upper_bound_predicate(self.variables[i]));
            }
        }

        self.slack = slack_lb + slack_ub - self.c;

        self.initialised = true;

        // check for satisfiability
        self.propagate(domains)
    }
}


