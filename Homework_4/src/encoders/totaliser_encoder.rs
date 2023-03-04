use crate::{basic_types::Literal, engine::ConstraintSatisfactionSolver};
use crate::basic_types::ClauseAdditionOutcome;

use super::EncodingStatus;

pub struct Pair {
    x1: Address,
    x2: Address,
    s: Vec<Option<Literal>>, // set of vars for each s
    c: Vec<Vec<Literal>>, // clauses for s (not used anymore)
    bound : usize,
}

pub enum Address {
    Address(Box<Pair>),
    Nil,
}

pub struct TotaliserEncoder {
    pair: Pair,
    k: usize,
}

impl Pair {
    pub fn new(mut literals: Vec<Literal>) -> Pair {

        if literals.len() == 0 {
            return Pair {
                x1: Address::Nil,
                x2: Address::Nil,
                s: Vec :: new(),
                c: Vec :: new(),
                bound : literals.len(),
            }
        }

        let part1 = literals.split_off(literals.len() / 2);
        let part2 = literals;
        if part1.len() + part2.len() != 1 {

            let left = Pair::new(part1.to_vec());
            let right = Pair::new(part2.to_vec());

            // init unary conditions
            let mut c : Vec<Vec<Literal>> = Vec :: new();
            let mut s : Vec<Option<Literal>> = Vec :: new();
            for _i in 0..(part1.len() + part2.len() + 1) { // add an s0
                s.push(None); // Only init, we don't know k yet
                c.push(Vec :: new());
            }

            let x1 = Address::Address(Box::new(right));
            let x2 = Address::Address(Box::new(left));
            let pair = Pair {
                x1,
                x2,
                s,
                c,
                bound : part1.len() + part2.len(),
            };
            pair

        } else {

            let mut c : Vec<Vec<Literal>> = Vec :: new();
            let mut s1 = Vec :: new();
            let mut s2 = Vec :: new();

            assert_eq!(part1.len(), 1);

            s1.push(!part1[0]);
            s1.push(part1[0]);

            s2.push(Some(part1[0]));
            s2.push(Some(!part1[0]));

            c.push(s1);

            let pair = Pair {
                x1 : Address::Nil,
                x2 : Address::Nil,
                s : s2,
                c,
                bound : part1.len(),
            };
            pair
        }
    }
}

impl TotaliserEncoder {

    /// Create a new totaliser encoder for the given literals. These literals form the left-hand
    /// side for the cardinality constraint which we want to encode. The right-hand side will be
    /// given when [`TotaliserEncoder::constrain_at_most_k`] is called.
    pub fn new(literals: Vec<Literal>) -> TotaliserEncoder {
        let mut literals_cop = literals.clone();

        for i in 0..literals_cop.len() {
            literals_cop[i] = !literals_cop[i]
        }

        return TotaliserEncoder {
            pair : Pair::new(literals_cop),
            k: literals.len() as usize,
        };
    }

    fn update_clauses(pair : &mut Pair, k : usize, k_old : usize, csp_solver: &mut ConstraintSatisfactionSolver) -> EncodingStatus {

        // init default childs
        let left : &Pair;
        let right : &Pair;

        // do this the first time
        if pair.bound != 1 {

            // extract neighbours and propagate
            match pair.x1 {
                Address::Address(ref mut left_ref) => {
                    TotaliserEncoder::update_clauses(left_ref, k, k_old, csp_solver);
                    left = left_ref;
                },
                _ => panic!("bound {:?}, we expect at least two pairs for len != 1", pair.bound),
            };

            match pair.x2 {
                Address::Address(ref mut right_ref) => {
                    TotaliserEncoder::update_clauses(right_ref, k, k_old, csp_solver);
                    right = right_ref;
                },
                _ => panic!("bound {:?}, we expect at least two pairs for len != 1", pair.bound),
            };

            // fill up s
            for i in 1..std::cmp::min(pair.s.len(), 2 * k + 1) {
                match pair.s[i] {
                    Some(_) => {},
                    _ => pair.s[i] = Some(Literal::new(
                        csp_solver.create_new_propositional_variable(), true)),
                };

                if i > 1 {
                    let mut implication = Vec :: new();
                    implication.push(!pair.s[i].unwrap());
                    implication.push(pair.s[i - 1].unwrap());
                    csp_solver.add_permanent_clause(implication); // sj+1 -> sj
                }
            }

            // extract clauses
            for i in 0..std::cmp::min(left.bound + 1, k + 1) {
                for j in 0..std::cmp::min(right.bound + 1, k + 1) { // p->q ==> (~p \/ q) ==> ((~xi \/ ~xj) \/ si+j)

                    let mut temp: Vec<Literal> = Vec::new();
                    if i != 0 {
                        temp.push(!left.s[i].unwrap());
                    }
                    if j != 0 {
                        temp.push(!right.s[j].unwrap());
                    }
                    if j + i != 0 {
                        temp.push(pair.s[i + j].unwrap());
                        csp_solver.add_permanent_clause(temp);
                    }
                }
            }
        }

        if k + 1 < pair.s.len() {
            match csp_solver.add_unit_clause(!pair.s[k + 1].unwrap()) {
                ClauseAdditionOutcome::Infeasible => return EncodingStatus::ConflictDetected,
                _ => {},
            };
        }

        // return status
        return EncodingStatus :: NoConflictDetected;
    }

    /// Add the constraint to the csp solver, and set the upper-bound to `k`. When called
    /// repeatidly, this method re-uses the encoding of previous calls. This only works when `k` is
    /// strictly decreasing in successive calls. Calling this method with a value `k` and then
    /// calling it again with value `k + 1` is undefined behavior.
    pub fn constrain_at_most_k(
        &mut self,
        k: usize,
        csp_solver: &mut ConstraintSatisfactionSolver,
    ) -> EncodingStatus {

        if k > self.k {
            panic!("k is larger, this is undefined for fun constrain_at_most_k")
        }

        let ref mut pair = self.pair;
        let status = TotaliserEncoder::update_clauses(pair, k, self.k, csp_solver);
        self.k = k;
        return status;
    }
}
