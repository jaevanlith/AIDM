use std::{collections::HashMap, time::Instant};

use crate::{
    basic_types::{ClauseAdditionOutcome, Function, Literal, WeightedLiteral},
    engine::ConstraintSatisfactionSolver,
    pumpkin_asserts::{pumpkin_assert_moderate, pumpkin_assert_simple},
};

use super::EncodingStatus;

//encodes the constraint \sum w_i x_i <= k

//implementation is done based on the paper:
//"Generalized totalizer encoding for pseudo-boolean constraints.", Joshi Saurabh, Ruben Martins, and Vasco Manquinho.  CP'15.
pub struct GeneralisedTotaliserEncoder {
    initial_weighted_literals: Vec<WeightedLiteral>, //original weighted literals as provided by the input function (without any preprocessing)
    internal_k: u64,      //the 'k' value after subtracting the root fixed cost
    root_fixed_cost: u64, //internal value that represents the left hands side at the root level
    index_last_added_weighted_literal: usize,
    layers: Vec<Layer>,
    num_clauses_added: usize,
}

impl GeneralisedTotaliserEncoder {
    pub fn new(
        function: &Function,
        csp_solver: &ConstraintSatisfactionSolver,
    ) -> GeneralisedTotaliserEncoder {
        let initial_weighted_literals =
            function.get_function_as_weighted_literals_vector(csp_solver);
        GeneralisedTotaliserEncoder {
            initial_weighted_literals,
            internal_k: u64::MAX,
            root_fixed_cost: function.get_constant_term(),
            index_last_added_weighted_literal: usize::MAX,
            layers: vec![],
            num_clauses_added: 0,
        }
    }

    pub fn constrain_at_most_k(
        &mut self,
        k: u64,
        csp_solver: &mut ConstraintSatisfactionSolver,
    ) -> EncodingStatus {
        pumpkin_assert_simple!(
            csp_solver
                .get_propositional_assignments()
                .is_at_the_root_level(),
            "Can only add encodings at the root level."
        );

        println!("c GTE k = {k}");

        if self.has_encoding() {
            self.decrease_k(k, csp_solver)
        } else {
            self.encode_at_most_k(k, csp_solver)
        }
    }
}

impl GeneralisedTotaliserEncoder {
    fn encode_at_most_k(
        &mut self,
        k: u64,
        csp_solver: &mut ConstraintSatisfactionSolver,
    ) -> EncodingStatus {
        let time_start = Instant::now();

        let weighted_literals = self.initialise(k, csp_solver);

        if weighted_literals.is_none() {
            println!(
                "c encoding added {} clauses to the solver.",
                self.num_clauses_added
            );

            println!(
                "c initial encoding took {} seconds.",
                time_start.elapsed().as_secs()
            );

            println!("c encoding detected conflict at the root!");

            return EncodingStatus::ConflictDetected;
        }

        let mut processed_terms = weighted_literals.unwrap();
        //at this point we have:
        //  1. relevant terms in 'processed terms'
        //      each term in unassigned
        //  2. updated internal k, which will be used to encode the constraint
        //  3. each weight will be at most k

        //special case when violations cannot exceed k
        //  in this case nothing needs to be done
        if processed_terms.iter().map(|p| p.weight).sum::<u64>() <= self.internal_k {
            println!(
                "c encoding added {} clauses to the solver.",
                self.num_clauses_added
            );
            println!(
                "c initial encoding took {} seconds.",
                time_start.elapsed().as_secs()
            );
            println!(
                "c encoder detected that the constraint is too lose, not totaliser tree needs to be encoded!"
            );
            return EncodingStatus::NoConflictDetected;
        }
        //a good heuristic is to sort the literals by weight with a stable ordering
        //  this reduces the size of the encoding significantly
        processed_terms.sort_by(|p1, p2| p1.weight.cmp(&p2.weight));

        //standard case
        self.encode_at_most_k_standard_case(processed_terms, csp_solver);

        println!(
            "c initial encoding took {} seconds.",
            time_start.elapsed().as_secs()
        );

        EncodingStatus::NoConflictDetected
    }

    //The log2 function of Rust is not yet considered stable
    //  so we do a brute force version here
    fn compute_logarithm_based_2(mut num: usize) -> usize {
        pumpkin_assert_simple!(num.is_power_of_two());

        let mut log_value = 0;
        while num > 0 {
            num /= 2;
            log_value += 1;
        }
        log_value
    }

    fn encode_at_most_k_standard_case(
        &mut self,
        processed_terms: Vec<WeightedLiteral>,
        csp_solver: &mut ConstraintSatisfactionSolver,
    ) {
        //the generalised totaliser encoding can be visualised as a binary tree
        //  the leaf nodes are the input literals
        //  each node above the leafs represents the sum of two child nodes, where each partial sum is represented by a new literal
        //  the final/root layer contains all feasible partial sums of the input variables
        //  Note each layer has half of the number of nodes as the previous layer but the number of partial sums (variables) can potentially grow exponentially

        //current layer is the layer that is being used to construct the next layer
        //  the next layer contains the literals that represent the partial sum of the current layer
        self.layers.push(Layer::new());
        //initially, each node in the layer consists of exactly one literal
        self.layers[0].nodes = processed_terms
            .iter()
            .map(|wl| vec![*wl])
            .collect::<Vec<Vec<WeightedLiteral>>>();

        //these are to be used in the loop below
        //  will be reused to avoid allocating each iteration
        let mut value_to_literal_map: HashMap<u64, Literal> = HashMap::new();
        let mut partial_sums: Vec<u64> = Vec::new();

        //  in each iteration, the literals of the next_layer are created and appropriate clauses are added to capture the partial sums
        for index_current_layer in 0..GeneralisedTotaliserEncoder::compute_logarithm_based_2(
            processed_terms.len().next_power_of_two(),
        ) {
            self.layers.push(Layer::new());
            let num_nodes_in_current_layer = self.layers[index_current_layer].nodes.len();

            //neighbouring nodes of the current layer are merged and their sum is represented in their parent node that is stored in the next layer
            //  we merge the first and the second node (merge_index = 0), then the third and the fourth node (merge_index = 1), and so on
            for merge_index in 0..num_nodes_in_current_layer / 2 {
                //these are the indicies of the two nodes that will be merged in this step
                let index_node1 = 2 * merge_index;
                let index_node2 = 2 * merge_index + 1;
                //the result of merge the two nodes will be stored in the next layer node
                let mut next_layer_node: Vec<WeightedLiteral> = Vec::new();

                //create new variables and record their indicies as appropriate
                //two stage process: identify partial sums and then create the literals

                //  first compute the necessary partial sums
                partial_sums.clear();

                //collect weights from node1
                for weighted_literal in &self.layers[index_current_layer].nodes[index_node1] {
                    pumpkin_assert_moderate!(weighted_literal.weight <= self.internal_k);
                    partial_sums.push(weighted_literal.weight);
                }
                //collect weight from node2
                for weighted_literal in &self.layers[index_current_layer].nodes[index_node2] {
                    pumpkin_assert_moderate!(weighted_literal.weight <= self.internal_k);
                    partial_sums.push(weighted_literal.weight);
                }
                //collect weights that could happen as a result of adding a weight from node1 and a weight from node 2
                for wl1 in &self.layers[index_current_layer].nodes[index_node1] {
                    for wl2 in &self.layers[index_current_layer].nodes[index_node2] {
                        let combined_weight = wl1.weight + wl2.weight;
                        if combined_weight <= self.internal_k {
                            partial_sums.push(combined_weight);
                        } else {
                            //can break the inner loop, since other values are only getting larger
                            break;
                        }
                    }
                }
                //at this point the vector 'partial sums' contains all partial sums
                //  but it may contain duplicates too
                //  remove the duplicates
                //  note that this is more efficient than using a HashSet
                partial_sums.sort();
                partial_sums.dedup();

                value_to_literal_map.clear();
                //  then create the variables, one for each partial sum, and register the mapping between the partial sum value and the corresponding literal
                for partial_sum in &partial_sums {
                    let variable = csp_solver.create_new_propositional_variable();
                    let literal = Literal::new(variable, true);
                    value_to_literal_map.insert(*partial_sum, literal);
                    next_layer_node.push(WeightedLiteral {
                        literal,
                        weight: *partial_sum,
                    });
                }

                //now perform the merge to define the new variables / summation

                //  define sums of one literal from node1
                //  node1[weight] -> next_layer_node[weight]
                for weighted_literal in &self.layers[index_current_layer].nodes[index_node1] {
                    csp_solver.add_permanent_implication_unchecked(
                        weighted_literal.literal,
                        *value_to_literal_map.get(&weighted_literal.weight).unwrap(),
                    );
                    self.num_clauses_added += 1;
                }
                //  define sums of one literal from node2
                //  node2[weight] -> next_layer_node[weight]
                for weighted_literal in &self.layers[index_current_layer].nodes[index_node2] {
                    csp_solver.add_permanent_implication_unchecked(
                        weighted_literal.literal,
                        *value_to_literal_map.get(&weighted_literal.weight).unwrap(),
                    );
                    self.num_clauses_added += 1;
                }
                //  define sums could happen as a result of adding a weight from node1 and a weight from node 2
                //  node1[weight1] + node2[weight2] -> next_layer_node[weight1 + weight2]
                for wl1 in &self.layers[index_current_layer].nodes[index_node1] {
                    for wl2 in &self.layers[index_current_layer].nodes[index_node2] {
                        let combined_weight = wl1.weight + wl2.weight;
                        if combined_weight <= self.internal_k {
                            csp_solver.add_permanent_ternary_clause_unchecked(
                                !wl1.literal,
                                !wl2.literal,
                                *value_to_literal_map.get(&combined_weight).unwrap(),
                            );
                            self.num_clauses_added += 1;
                        //explicitly forbid the assignment of both literals
                        //  note: could look into improving this part with implications weight[i] -> weight[i-1], could be a good trade-off
                        //  todo check if these clauses are necessary, and see if the trade-off makes sense
                        //      I think it is necessary
                        } else {
                            csp_solver
                                .add_permanent_implication_unchecked(wl1.literal, !wl2.literal);
                            self.num_clauses_added += 1;
                        }
                    }
                }
                //add the node to the next layer
                self.layers[index_current_layer + 1]
                    .nodes
                    .push(next_layer_node);
            } //node merging done

            //copy over the odd-numbered node that will not merge this round
            //  recall that the number of nodes in a layer may be an odd number
            //      since we merge nodes in pairs, it follows that one node will be unmerged
            //      so we just copy the unmerged node to the next layer
            if num_nodes_in_current_layer % 2 == 1 {
                //the unmerged node will be the last node in the current layer
                let unmerged_node = self.layers[index_current_layer]
                    .nodes
                    .last()
                    .unwrap()
                    .clone();

                self.layers[index_current_layer + 1]
                    .nodes
                    .push(unmerged_node);
            }
        }

        //the last layer now stores the final sum literals
        //  i.e., if the sum of input literals is at least k, then at least the weighted literal with weight k will be set to true
        //  note that there may be holes, so if a literal with weight m_1 is set to true, it may not be the case that literal with weight m_2 with m_2 < m_1 is also set to true
        //      this is a difference when compared to the standard unweighted totaliser
        //      however this is not an issue, since in the above discussion, at least the weight with weight k will be set to true, so we can use that to constrain

        self.index_last_added_weighted_literal = self.layers.last().unwrap().nodes[0].len();

        println!(
            "c encoding added {} clauses to the solver.",
            self.num_clauses_added
        );
    }

    fn has_encoding(&self) -> bool {
        !self.layers.is_empty()
    }

    //the second value of the tuple is the unassigned weighted literals that should be considered
    fn initialise(
        &mut self,
        input_k: u64,
        csp_solver: &mut ConstraintSatisfactionSolver,
    ) -> Option<Vec<WeightedLiteral>> {
        //note that the code could potentially be implemented more efficiently, e.g., doing initialisation in one loop as opposed to several loops
        //  however not sure if that is a bottleneck

        //it may be beneficial to consider negating the literals
        //  for simplicity we ignore this, could revisit later
        //  in that case, when strengthening the constraint incrementality, we would need to take into account whether or not negation took place!

        //literals that are assigned at the root level can be removed from the encoding
        //  literals that evaluate to false can be ignored
        //  literals that evaluate to true can be removed from consideration, but the k value needs to be updated accordingly

        //  here we compute the left hand side value cause by literals assigned to true at the root level
        //      note: during initialisation, we took into account the constant term of the input function (see 'new'), so here we only need to add the root cost associated with root literals
        self.root_fixed_cost += self
            .initial_weighted_literals
            .iter()
            .filter_map(|p| {
                if csp_solver
                    .get_propositional_assignments()
                    .is_literal_assigned_true(p.literal)
                {
                    Some(p.weight)
                } else {
                    None
                }
            })
            .sum::<u64>();

        //  if the violations at the root make the constraint infeasible, report and stop
        if self.root_fixed_cost > input_k {
            return None;
        }
        //k is then updated to take into account the root fixed cost
        self.internal_k = input_k - self.root_fixed_cost;

        //propagate unassigned terms whose violation would exceed k
        for term in &self.initial_weighted_literals {
            if term.weight > self.internal_k
                && csp_solver
                    .get_propositional_assignments()
                    .is_literal_unassigned(term.literal)
            {
                let status = csp_solver.add_unit_clause(!term.literal);
                self.num_clauses_added += 1;

                if let ClauseAdditionOutcome::Infeasible = status {
                    return None;
                }
            }
        }

        //remove literals assigned at the root from consideration
        Some(
            self.initial_weighted_literals
                .iter()
                .filter_map(|p| {
                    if csp_solver
                        .get_propositional_assignments()
                        .is_literal_unassigned(p.literal)
                    {
                        Some(*p)
                    } else {
                        None
                    }
                })
                .collect(),
        )
    }

    fn decrease_k(
        &mut self,
        new_k: u64,
        csp_solver: &mut ConstraintSatisfactionSolver,
    ) -> EncodingStatus {
        //note that there is a discrepancy between new_k (k given as input) and the internal_k
        //  the internal_k is computed as input_k - unavoidable_violations
        //  recall that unavoidable violations refer to the constant term in the original function and any violations at the root level
        pumpkin_assert_simple!(
            self.has_encoding() && new_k - self.root_fixed_cost < self.internal_k,
            "We expect k will be strictly decreasing!"
        );
        pumpkin_assert_simple!(self.index_last_added_weighted_literal > 0);
        pumpkin_assert_simple!(self.root_fixed_cost <= new_k); //not an error per-se but in the current implementation it would be odd to have this assert fail
        pumpkin_assert_simple!(
            !self.layers.is_empty() && self.layers.last().unwrap().nodes.len() == 1
        );

        self.internal_k = new_k - self.root_fixed_cost;

        //the literals in each layer are sorted by weight
        //  this is a by-product of the above implementation
        //  this is used by the loop below
        let weighted_literals = &self.layers.last().unwrap().nodes[0];

        self.index_last_added_weighted_literal = weighted_literals.len();

        for i in (0..self.index_last_added_weighted_literal).rev() {
            //forbid all literals that exceed k
            //  this is now implemented in a linear fashion
            //      possibly could do binary search, but for simplicity this will do
            //      although for binary search need to make sure that implications hold with output literals
            if weighted_literals[i].weight > self.internal_k {
                let status = csp_solver.add_unit_clause(!weighted_literals[i].literal);
                self.num_clauses_added += 1;
                self.index_last_added_weighted_literal = i;

                if let ClauseAdditionOutcome::Infeasible = status {
                    return EncodingStatus::ConflictDetected;
                }
            } else {
                //the first time a literal no longer exceeds k, we can stop
                //  since other literals down the line have smaller weights
                break;
            }
        }
        EncodingStatus::NoConflictDetected
    }
}

struct Layer {
    pub nodes: Vec<Vec<WeightedLiteral>>,
}

impl Layer {
    pub fn new() -> Layer {
        Layer { nodes: vec![] }
    }
}
