#!/usr/bin/env python
import argparse
import subprocess
import json
import os

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


def check_unsat(binary_path, instance_path):
    result = subprocess.run([binary_path, f'-file-location={instance_path}'], capture_output=True)
    if result.returncode != 0:
        return f'Solver has terminated with error code {result.return_code}'
    result_msg = None
    for line in result.stdout.decode('utf-8').split('\n'):
        if line.strip() == '':
            continue
        elif line.startswith('c'):
            continue
        elif line.startswith('s'):
            if line.strip() != 's UNSATISFIABLE':
                result_msg = f'Unexpected result at line {line}'
                break
        else:
            result_msg = f'Malformed output at line {line}'
            break
    return result_msg


def validate_assignment(instance_path, assignment):
    n_vars, n_clauses = None, None
    with open(instance_path, 'r') as instance:
        for line in instance:
            if line.strip() == '':
                continue
            elif line.startswith('c'):
                continue
            elif line.startswith('p cnf'):
                n_vars, n_clauses = (int(x) for x in line.replace('p cnf', '').split())
            else:
                assert n_vars is not None and n_clauses is not None
                clause = [int(x) for x in line.split()]
                assert clause[-1] == 0
                clause = clause[:-1]
                if any(x in assignment for x in clause):
                    continue
                else:
                    return f'Assignment was falsified by clause {line}'


def check_sat(binary_path, instance_path):
    result = subprocess.run([binary_path, f'-file-location={instance_path}'], capture_output=True)
    if result.returncode != 0:
        return f'Solver has terminated with error code {result.return_code}'
    result_msg = None
    assignment = list()
    for line in result.stdout.decode('utf-8').split('\n'):
        if line.strip() == '':
            continue
        elif line.startswith('c'):
            continue
        elif line.startswith('s'):
            if line.strip() != 's SATISFIABLE':
                result_msg = f'Unexpected result at line {line}'
                break
        elif line.startswith('v 0'):
            assignment = [int(lit) for lit in line.replace('v 0', '').split()]
        else:
            result_msg = f'Malformed output at line {line}'
            break
    if result_msg is not None:
        return result_msg
    else:
        return validate_assignment(instance_path, assignment)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('-s', '--sat-instances', type=str, nargs='*', default=[])
    parser.add_argument('-u', '--unsat-instances', type=str, nargs='*', default=[])
    args = parser.parse_args()
    instances = [(path, True) for path in args.sat_instances] + [(path, False) for path in args.unsat_instances]
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
    for instance_path, is_sat in instances:
        msg = None
        if is_sat:
            print(f'{TermColors.UNDERLINE}Testing a satisfiable instance {instance_path}{TermColors.ENDC}', end=' ... ')
            msg = check_sat(binary_path, instance_path)
        else:
            print(f'{TermColors.UNDERLINE}Testing an unsatisfiable instance {instance_path}{TermColors.ENDC}', end=' ... ')
            msg = check_unsat(binary_path, instance_path)
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
