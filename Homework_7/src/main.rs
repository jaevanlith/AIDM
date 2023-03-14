#![allow(dead_code)] //turn off dead code warnings for now, later to be removed

mod arguments;
mod basic_types;
mod encoders;
mod engine;
mod propagators;
mod pumpkin_asserts;

use basic_types::*;
use engine::*;

fn main() {
    pumpkin_asserts::print_pumpkin_assert_warning_message!();

    let mut argument_handler = Pumpkin::create_argument_handler();
    argument_handler.print_help_summary_if_needed_and_exit();
    argument_handler.parse_command_line_arguments();

    let file_location = argument_handler.get_string_argument("file-location");

    if file_location.is_empty() {
        println!("No file location given. Aborting.");
        std::process::abort();
    }

    let file_format = if file_location.ends_with(".cnf") {
        FileFormat::CnfDimacsPLine
    } else if file_location.ends_with(".wcnf") {
        FileFormat::WcnfDimacsPLine
    } else {
        panic!("Unknown file format!")
    };

    let mut pumpkin = Pumpkin::new(&argument_handler);
    pumpkin.read_file(file_location.as_str(), file_format);
    pumpkin.reset_variable_selection(argument_handler.get_integer_argument("random-seed"));

    let pumpkin_output = pumpkin.solve();

    match pumpkin_output {
        PumpkinExecutionFlag::Feasible { feasible_solution } => {
            println!("s SATISFIABLE");
            println!("v {}", stringify_solution(&feasible_solution));
        }
        PumpkinExecutionFlag::Optimal { optimal_solution } => {
            println!("s OPTIMAL");
            println!("o {}", optimal_solution.objective_value);
            println!("v {}", stringify_solution(&optimal_solution.solution));
        }
        PumpkinExecutionFlag::Infeasible => println!("s UNSATISFIABLE"),
        PumpkinExecutionFlag::Timeout => println!("s UNKNOWN"),
    }
}

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
