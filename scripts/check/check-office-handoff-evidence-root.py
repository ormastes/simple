#!/usr/bin/env python3
"""Check the Office handoff's source path contract, without running the UI gate.

Evaluates only the actual string-concatenation expressions from the two owners.
This is host contract evidence, not Simple runtime or Office acceptance evidence.
"""
import ast
from pathlib import Path
import re


ROOT = Path(__file__).resolve().parents[2]
GATE = ROOT / "scripts/check/check-office-cli-tui-ui-access.spl"
SPEC = ROOT / "test/03_system/plan_acceptance/office_cli_tui_ui_access_spec.spl"


def expression(source, pattern):
    matches = re.findall(pattern, source, re.MULTILINE)
    if len(matches) != 1:
        raise AssertionError(f"Expected exactly one owner expression: {pattern}")
    return matches[0].strip()


def evaluate(text, bindings):
    def visit(node):
        if isinstance(node, ast.Constant) and isinstance(node.value, str):
            return node.value
        if isinstance(node, ast.Name):
            return bindings[node.id]
        if isinstance(node, ast.BinOp) and isinstance(node.op, ast.Add):
            return visit(node.left) + visit(node.right)
        raise AssertionError(f"Unsupported path expression: {text}")
    return visit(ast.parse(text, mode="eval").body)


def roots(gate, spec, run_id):
    writer_base = expression(gate, r'^val EVIDENCE_BASE: text = (.+)$')
    reader_base = expression(spec, r'^val OFFICE_UI_BASE: text = (.+)$')
    writer = expression(gate, r'^fn _run_root\(run_id: text\) -> text:\n    (.+)$')
    reader = expression(spec, r'^    val root = (OFFICE_UI_BASE .+)$')
    return (
        evaluate(writer, {"EVIDENCE_BASE": evaluate(writer_base, {}), "run_id": run_id}),
        evaluate(reader, {"OFFICE_UI_BASE": evaluate(reader_base, {}), "run_id": run_id}),
    )


def check(gate, spec):
    # Ensure both owners use the run ID supplied to the actual gate invocation.
    assert '"--run-id", run_id' in spec
    assert 'val root = _run_root(run_id)' in gate
    assert '"handoff-" + _run_id()' in spec
    suffixes = set(re.findall(r'(?:file_read|file_exists)\(root \+ "([^"]+)"\)', spec))
    assert "/suite.txt" in suffixes and "/perf/startup.txt" in suffixes
    previous = None
    for run_id in ("handoff-plan-remains-run-a", "handoff-plan-remains-run-b"):
        writer, reader = roots(gate, spec, run_id)
        assert writer == reader, f"Writer {writer!r} != reader {reader!r}"
        assert reader != previous, "Different runs must not share evidence"
        for suffix in suffixes:
            assert Path(writer + suffix) == Path(reader + suffix)
        previous = reader
    return len(suffixes)


if __name__ == "__main__":
    gate, spec = GATE.read_text(encoding="utf-8"), SPEC.read_text(encoding="utf-8")
    count = check(gate, spec)
    # Restore the exact reported wrong base: the contract must reject it.
    old = re.sub(r'^val OFFICE_UI_BASE: text = .+$',
                 'val OFFICE_UI_BASE: text = "build/test-artifacts/03_system/plan_acceptance/office_cli_tui_ui_access/runs/"',
                 spec, flags=re.MULTILINE)
    try:
        check(gate, old)
    except AssertionError:
        print(f"PASS: {count} receipt paths, two isolated runs; historical mismatch rejected")
    else:
        raise AssertionError("Historical wrong-root negative control passed")
