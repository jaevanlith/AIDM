use crate::{
    basic_types::{
        EnqueueStatus, IntegerVariable, Predicate, PropagationStatusCP, PropositionalConjunction,
    },
    engine::DomainManager,
};

use super::ConstraintProgrammingPropagator;

/// Propagator for the constraint \sum w_i * x_i >= c.
///
/// Note: Even though the domains of integer variables are represented as signed integers, expect
/// them to be unsigned values. Calling the propagator with variables which have negative bounds on
/// their domains can be considered undefined behaviour.
pub struct LinearInequalityPropagator {
    // Add any fields here you need.
}

impl LinearInequalityPropagator {
    pub fn new(
        weights: Vec<i64>,
        variables: Vec<IntegerVariable>,
        c: i64,
    ) -> LinearInequalityPropagator {
        assert_eq!(weights.len(), variables.len(), 
            "Expect the number of weights to match the number of variables for the linear inequality propagator.");

        LinearInequalityPropagator {
            // Initialise the fields
        }
    }
}

impl ConstraintProgrammingPropagator for LinearInequalityPropagator {
    fn propagate(&mut self, domains: &mut DomainManager) -> PropagationStatusCP {
        todo!()
    }

    fn synchronise(&mut self, _domains: &DomainManager) {
        // Left blank, it is not necessary to use this. However, if you want to, you can.
    }

    fn notify_lower_bound_integer_variable_change(
        &mut self,
        integer_variable: IntegerVariable,
        old_lower_bound: i32,
        new_lower_bound: i32,
        domains: &DomainManager,
    ) -> EnqueueStatus {
        todo!()
    }

    fn notify_upper_bound_integer_variable_change(
        &mut self,
        integer_variable: IntegerVariable,
        old_upper_bound: i32,
        new_upper_bound: i32,
        domains: &DomainManager,
    ) -> EnqueueStatus {
        todo!()
    }

    fn notify_domain_hole_integer_variable_change(
        &mut self,
        integer_variable: IntegerVariable,
        removed_value_from_domain: i32,
        domains: &DomainManager,
    ) -> EnqueueStatus {
        todo!()
    }

    fn get_reason_for_propagation(&mut self, predicate: Predicate) -> PropositionalConjunction {
        unreachable!()
    }

    fn priority(&self) -> u32 {
        0
    }

    fn name(&self) -> &str {
        "linear programming propagator"
    }

    fn get_integer_variables_to_watch_for_lower_bound_changes(&self) -> Vec<IntegerVariable> {
        todo!()
    }

    fn get_integer_variables_to_watch_for_upper_bound_changes(&self) -> Vec<IntegerVariable> {
        todo!()
    }

    fn get_integer_variables_to_watch_for_domain_hole_changes(&self) -> Vec<IntegerVariable> {
        todo!()
    }

    fn initialise_at_root(&mut self, domains: &mut DomainManager) -> PropagationStatusCP {
        todo!()
    }
}

