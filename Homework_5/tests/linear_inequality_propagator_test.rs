use std::ops::RangeInclusive;

use pumpkin::{
    basic_types::{EnqueueStatus, PropagationStatusCP},
    engine::{AssignmentsInteger, DomainManager},
    propagators::{ConstraintProgrammingPropagator, LinearInequalityPropagator},
};

#[test]
fn test_variables_are_registered_for_bounds_changes() {
    let mut assignment = AssignmentsInteger::new();

    let weights = vec![-4, 3, -2, 2];
    let vars = (0..weights.len())
        .map(|_| assignment.grow(0, 9))
        .collect::<Vec<_>>();

    let propagator = LinearInequalityPropagator::new(weights, vars.clone(), -9);
    assert_eq!(
        vec![vars[0], vars[2]],
        propagator.get_integer_variables_to_watch_for_lower_bound_changes()
    );
    assert_eq!(
        vec![vars[1], vars[3]],
        propagator.get_integer_variables_to_watch_for_upper_bound_changes()
    );
    assert!(propagator
        .get_integer_variables_to_watch_for_domain_hole_changes()
        .is_empty());
}

#[test]
fn test_lower_bound_changes_causes_enqueue() {
    let mut assignment = AssignmentsInteger::new();

    let weights = vec![-4, 3, -2, 2];
    let vars = (0..weights.len())
        .map(|_| assignment.grow(0, 9))
        .collect::<Vec<_>>();

    let mut propagator = LinearInequalityPropagator::new(weights, vars.clone(), -9);
    let mut domains = DomainManager::new(0, &mut assignment);

    // The propagator is bounds-consistent, so no need to enqueue when domain holes are introduced.
    // In fact, this should never happen since the propagator should not register any variables for
    // which this event is relevant. However, we test it here as a fallback since the method needs
    // to be implemented by the trait.
    for &var in vars.iter() {
        assert_eq!(
            EnqueueStatus::DoNotEnqueue,
            propagator.notify_domain_hole_integer_variable_change(var, 2, &mut domains)
        );
    }

    for var in vec![vars[0], vars[2]] {
        assert_eq!(
            EnqueueStatus::ShouldEnqueue,
            propagator.notify_lower_bound_integer_variable_change(var, 0, 2, &mut domains)
        );
    }

    for var in vec![vars[1], vars[3]] {
        assert_eq!(
            EnqueueStatus::ShouldEnqueue,
            propagator.notify_upper_bound_integer_variable_change(var, 9, 7, &mut domains)
        );
    }
}

#[test]
fn test_domains_are_tightened_after_propagation_1() {
    let weights = vec![-4, -3, -2];
    let c = -9;
    let initial_domains = vec![0..=9, 0..=9, 0..=9];
    let propagated_domains = vec![0..=2, 0..=3, 0..=4];

    test_propagation_scenario_no_conflict(weights, c, initial_domains, propagated_domains);
}

#[test]
fn test_domains_are_tightened_after_propagation_2() {
    let weights = vec![2, 5];
    let c = 12;
    let initial_domains = vec![0..=10, 0..=2];
    let propagated_domains = vec![1..=10, 0..=2];

    test_propagation_scenario_no_conflict(weights, c, initial_domains, propagated_domains);
}

#[test]
fn test_domains_are_tightened_after_propagation_3() {
    let weights = vec![-4, 20];
    let c = 0;
    let initial_domains = vec![12..=50, 0..=10];
    let propagated_domains = vec![12..=50, 3..=10];

    test_propagation_scenario_no_conflict(weights, c, initial_domains, propagated_domains);
}

#[test]
fn test_conflict_is_detected_1() {
    let weights = vec![-4, -3, -2];
    let c = -9;
    let initial_domains = vec![1..=9, 1..=9, 2..=9];

    test_propagation_scenario_with_conflict(weights, c, initial_domains);
}

#[test]
fn test_conflict_is_detected_2() {
    let weights = vec![2, 5];
    let c = 12;
    let initial_domains = vec![0..=3, 0..=1];

    test_propagation_scenario_with_conflict(weights, c, initial_domains);
}

#[test]
fn test_conflict_is_detected_3() {
    let weights = vec![-4, 20];
    let c = 0;
    let initial_domains = vec![12..=50, 0..=2];

    test_propagation_scenario_with_conflict(weights, c, initial_domains);
}

fn test_propagation_scenario_no_conflict(
    weights: Vec<i64>,
    c: i64,
    initial_domains: Vec<RangeInclusive<i32>>,
    propagated_domains: Vec<RangeInclusive<i32>>,
) {
    assert_eq!(weights.len(), initial_domains.len());
    assert_eq!(weights.len(), propagated_domains.len());

    let normal_prop = |mut propagator: LinearInequalityPropagator, domains: &mut DomainManager| {
        propagator.propagate(domains)
    };
    let init_at_root = |mut propagator: LinearInequalityPropagator, domains: &mut DomainManager| {
        propagator.initialise_at_root(domains)
    };

    for action in [normal_prop, init_at_root] {
        let mut assignment = AssignmentsInteger::new();

        let vars = initial_domains
            .iter()
            .map(|domain| assignment.grow(*domain.start(), *domain.end()))
            .collect::<Vec<_>>();

        {
            let mut domain_manager = DomainManager::new(0, &mut assignment);
            let propagator = LinearInequalityPropagator::new(weights.clone(), vars.clone(), c);

            assert_eq!(
                PropagationStatusCP::NoConflictDetected,
                action(propagator, &mut domain_manager)
            );
        }

        for (&var, domain) in vars.iter().zip(propagated_domains.iter()) {
            assert_eq!(*domain.start(), assignment.get_lower_bound(var));
            assert_eq!(*domain.end(), assignment.get_upper_bound(var));
        }
    }
}

fn test_propagation_scenario_with_conflict(
    weights: Vec<i64>,
    c: i64,
    initial_domains: Vec<RangeInclusive<i32>>,
) {
    assert_eq!(weights.len(), initial_domains.len());

    let normal_prop = |mut propagator: LinearInequalityPropagator, domains: &mut DomainManager| {
        propagator.propagate(domains)
    };
    let init_at_root = |mut propagator: LinearInequalityPropagator, domains: &mut DomainManager| {
        propagator.initialise_at_root(domains)
    };

    for action in [normal_prop, init_at_root] {
        let mut assignment = AssignmentsInteger::new();

        let vars = initial_domains
            .iter()
            .map(|domain| assignment.grow(*domain.start(), *domain.end()))
            .collect::<Vec<_>>();

        let mut domain_manager = DomainManager::new(0, &mut assignment);
        let propagator = LinearInequalityPropagator::new(weights.clone(), vars.clone(), c);

        assert!(matches!(
            action(propagator, &mut domain_manager),
            PropagationStatusCP::ConflictDetected { .. }
        ));
    }
}
