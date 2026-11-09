#!/usr/bin/env python3
"""Exercise the actual Actions conditions, including implicit-status hazards."""
import ast
import pathlib
import re
import yaml

root = pathlib.Path(__file__).resolve().parents[2]
workflow = yaml.safe_load((root / '.github/workflows/rust-tests.yml').read_text())
steps = {step.get('name'): step for step in workflow['jobs']['test']['steps']}
compile_step = steps['Compile compiler lib tests']
unit = steps['Execute exact LLVM pipeline strict HIR regression']
blocked = steps['Record blocked strict HIR prerequisite']
upload = steps['Retain strict HIR unit source and execution evidence']


def route(step, cancelled, runner_os, outcome):
    expression = step['if'].strip().removeprefix('${{').removesuffix('}}').strip()
    assert 'cancelled()' in expression, 'must override implicit success() without ignoring cancellation'
    expression = expression.replace('cancelled()', 'cancelled').replace('runner.os', 'runner_os')
    expression = expression.replace('steps.compiler_lib_tests.outcome', 'outcome').replace('&&', ' and ')
    expression = re.sub(r'!(?!=)', ' not ', expression).strip()
    tree = ast.parse(expression, mode='eval')
    allowed = (ast.Expression, ast.BoolOp, ast.And, ast.UnaryOp, ast.Not, ast.Compare,
               ast.Eq, ast.NotEq, ast.Name, ast.Constant, ast.Load)
    assert all(isinstance(node, allowed) for node in ast.walk(tree))
    assert all(node.id in {'cancelled', 'runner_os', 'outcome'} for node in ast.walk(tree) if isinstance(node, ast.Name))
    return eval(compile(tree, '<actual-workflow-condition>', 'eval'), {'__builtins__': {}},
                dict(cancelled=cancelled, runner_os=runner_os, outcome=outcome))


assert compile_step['id'] == 'compiler_lib_tests'
assert compile_step['run'] == 'cargo test -p simple-compiler --verbose --lib --no-run'
assert '--no-fail-fast' in steps['Run tests']['run']
assert not steps['Run tests'].get('continue-on-error', False)
assert not compile_step.get('continue-on-error', False)
assert not unit.get('continue-on-error', False)
assert unit['timeout-minutes'] == 3
assert route(compile_step, False, 'Linux', 'skipped')  # even after earlier workspace failure
assert route(unit, False, 'Linux', 'success')
assert not route(blocked, False, 'Linux', 'success')
for outcome in ('failure', 'skipped', 'cancelled'):
    assert not route(unit, False, 'Linux', outcome)
    assert route(blocked, False, 'Linux', outcome)
    assert route(upload, False, 'Linux', outcome)
for step in (compile_step, unit, blocked, upload):
    assert not route(step, True, 'Linux', 'success')
    assert not route(step, True, 'Linux', 'failure')
    assert not route(step, False, 'macOS', 'success')
assert steps['Checkout code']['with']['ref'] == '${{ github.sha }}'
for job in workflow['jobs'].values():
    for step in job.get('steps', []):
        action = step.get('uses', '')
        if action.startswith('actions/checkout@'): assert action == 'actions/checkout@v5'
        if action.startswith('actions/cache@'): assert action == 'actions/cache@v5'
        if action.startswith('actions/upload-artifact@'): assert action == 'actions/upload-artifact@v6'
print('PASS: actual workflow failure/success/cancellation routing, status preservation and Node24 actions')
