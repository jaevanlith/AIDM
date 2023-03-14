#!/usr/bin/env python
import argparse
import subprocess
import json
import os
from pathlib import Path

class TermColors:
    HEADER = '\033[95m'
    OKBLUE = '\033[94m'
    OKCYAN = '\033[96m'
    OKGREEN = '\033[92m'
    WARNING = '\033[93m'
    FAIL = '\033[91m'
    ENDC = '\033[0m'
    BOLD = '\033[1m'
    UNDERLINE = '\033[4m'


def run_cargo_build():
    result = subprocess.run(['cargo', 'build', '--release'], capture_output=True)
    stdout = result.stdout
    return_code = result.returncode
    print(stdout.decode('utf-8'))
    return return_code == 0

def run_cargo_test():
    result = subprocess.run(['cargo', 'test'], capture_output=True)
    stdout = result.stdout
    return_code = result.returncode
    print(stdout.decode('utf-8'))
    return return_code == 0


def try_find_binary():
    result = subprocess.run(['cargo', 'metadata', '--format-version', '1'], capture_output=True)
    obj = json.loads(result.stdout.decode('utf-8'))
    target_dir = obj['target_directory']
    return os.path.join(target_dir, 'release', 'pumpkin')


def validate_wcnf_assignment(instance_path, assignment, objective_value):
    n_vars, n_clauses, hard_weight = None, None, None
    evaluated_objective = 0

    with open(instance_path, 'r') as instance:
        for line in instance:
            if line.strip() == '':
                continue
            elif line.startswith('c'):
                continue
            elif line.startswith('p wcnf'):
                n_vars, n_clauses, hard_weight = (int(x) for x in line.replace('p wcnf', '').split())
            else:
                assert n_vars is not None and n_clauses is not None
                tokens = [int(x) for x in line.split()]
                weight = tokens[0]
                clause = tokens[1:]
                assert clause[-1] == 0
                clause = clause[:-1]
                if any(x in assignment for x in clause):
                    continue
                elif weight == hard_weight:
                    return f'Assignment was falsified by clause {line}'
                else:
                    evaluated_objective += weight

    if evaluated_objective != objective_value:
        return f'Evaluated objective {evaluated_objective} does not match reported objective {objective_value}'

def check_opt(binary_path, instance_path):
    result = subprocess.run([binary_path, f'-file-location={instance_path}'], capture_output=True)
    if result.returncode != 0:
        return f'Solver has terminated with error code {result.return_code}'

    lines = iter(result.stdout.decode('utf-8').split('\n'))
    line = next(lines)
    while line.strip() != "s OPTIMAL":
        line = next(lines)

    objective_line = next(lines).strip()
    assignment_line = next(lines).strip()

    if not objective_line.startswith("o ") or not assignment_line.startswith("v "):
        return f"Invalid output for {instance_path}"

    objective = int(objective_line.split(" ")[1])
    expected_objective = int(instance_path.name.split(".")[-2])
    if objective != expected_objective:
        return f"Reported objective value {objective} is not the optimal value {expected_objective}"

    assignment = assignment_line.replace("v ", "")
    assignment = [int(x) for x in assignment.split()]

    return validate_wcnf_assignment(instance_path, assignment, objective)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('instances', type=Path, nargs="+", help="The instances to check. Use wildcard if appropriate.")
    args = parser.parse_args()
    print(f'{TermColors.UNDERLINE}Building project{TermColors.ENDC}')
    if not run_cargo_build():
        print(f'{TermColors.FAIL}`cargo build` failed, terminating.{TermColors.ENDC}')
        return
    print(f'{TermColors.UNDERLINE}Running cargo test{TermColors.ENDC}')
    if not run_cargo_test():
        print(f'{TermColors.FAIL}`cargo test` failed, terminating.{TermColors.ENDC}')
        return
    print(f'{TermColors.OKGREEN}`cargo test` passed{TermColors.ENDC}')
    print()
    binary_path = try_find_binary()
    print(f'Located binary at {binary_path}, proceeding to testing on instances ...')
    print()
    for instance_path in args.instances:
        print(f'{TermColors.UNDERLINE}Testing instance {instance_path}{TermColors.ENDC}', end=' ... ')
        msg = check_opt(binary_path, instance_path)
        if msg is not None:
            print()
            print(f'{TermColors.FAIL}{msg}{TermColors.ENDC}')
            break
        else:
            print('passed')
    else:
        print()
        print(f'{TermColors.OKGREEN}All tests have been passed!{TermColors.ENDC}')


if __name__ == '__main__':
    main()
