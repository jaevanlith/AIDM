use pumpkin::{
    self,
    basic_types::{ClauseAdditionOutcome, Literal},
    encoders::{EncodingStatus, TotaliserEncoder},
    engine::{ConstraintSatisfactionSolver, Pumpkin},
};

use rand::{seq::SliceRandom, Rng};

#[test]
fn test_totaliser_encoder_encodes_cardinality_constraint() {
    let mut rng = rand::thread_rng();

    for _ in 0..50 {
        let mut csp_solver = ConstraintSatisfactionSolver::new(&Pumpkin::create_argument_handler());

        let n = rng.gen_range(2..100);
        let k = rng.gen_range(1..n);

        let mut literals =
            std::iter::from_fn(|| Some(csp_solver.create_new_propositional_variable()))
                .map(|var| Literal::new(var, true))
                .take(n)
                .collect::<Vec<_>>();

        let mut encoder = TotaliserEncoder::new(literals.clone());
        assert_eq!(
            EncodingStatus::NoConflictDetected,
            encoder.constrain_at_most_k(k, &mut csp_solver)
        );

        literals.shuffle(&mut rng);
        let true_lits = &literals[..k];
        let false_lits = &literals[k..];

        // The first `k` literals that are set to true should not trigger a conflict when added to
        // the solver.
        for &lit in true_lits {
            assert_eq!(
                ClauseAdditionOutcome::NoConflictDetected,
                csp_solver.add_unit_clause(lit)
            );
        }

        // The `k+1`th literal which is set to true should trigger a conflict when added to the
        // solver.
        assert_eq!(
            ClauseAdditionOutcome::Infeasible,
            csp_solver.add_unit_clause(false_lits[0])
        );

        // When `k` literals are set to true, the remaining `n-k` literals should be propagated to
        // false.
        for &lit in false_lits {
            assert!(csp_solver
                .get_propositional_assignments()
                .is_literal_assigned_false(lit));
        }
    }
}

#[test]
fn test_totaliser_encoder_constraint_can_be_incrementally_strengthened() {
    let mut rng = rand::thread_rng();

    for _ in 0..50 {
        let mut csp_solver = ConstraintSatisfactionSolver::new(&Pumpkin::create_argument_handler());

        let n = rng.gen_range(3..100);
        let k1 = rng.gen_range(2..n);
        let k2 = rng.gen_range(1..k1);

        let mut literals =
            std::iter::from_fn(|| Some(csp_solver.create_new_propositional_variable()))
                .map(|var| Literal::new(var, true))
                .take(n)
                .collect::<Vec<_>>();

        let mut encoder = TotaliserEncoder::new(literals.clone());
        assert_eq!(
            EncodingStatus::NoConflictDetected,
            encoder.constrain_at_most_k(k1, &mut csp_solver)
        );

        literals.shuffle(&mut rng);
        let true_lits = &literals[..k2];

        // The first `k2` literals that are set to true should not trigger a conflict when added to
        // the solver.
        for &lit in true_lits {
            assert_eq!(
                ClauseAdditionOutcome::NoConflictDetected,
                csp_solver.add_unit_clause(lit)
            );
        }

        for k in (k2..k1).rev() {
            assert_eq!(
                EncodingStatus::NoConflictDetected,
                encoder.constrain_at_most_k(k, &mut csp_solver)
            );
        }

        assert_eq!(
            EncodingStatus::ConflictDetected,
            encoder.constrain_at_most_k(k2 - 1, &mut csp_solver)
        );
    }
}
