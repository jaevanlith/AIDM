use pumpkin::basic_types::*;
use pumpkin::engine::*;

fn main() {
    pumpkin::print_pumpkin_assert_warning_message!();

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

            let values = (0..feasible_solution.num_propositional_variables())
                .map(|index| PropositionalVariable::new(index.try_into().unwrap()))
                .map(|var| {
                    if feasible_solution[var] {
                        format!("{} ", var.index())
                    } else {
                        format!("-{} ", var.index())
                    }
                })
                .collect::<String>();

            println!("v {}", values);
        }
        PumpkinExecutionFlag::Infeasible => println!("s UNSATISFIABLE"),
        PumpkinExecutionFlag::Timeout => println!("s UNKNOWN"),
    }
}
