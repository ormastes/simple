#!/usr/bin/env python3
"""Compile the bootstrap atomic helper and actual owner call expressions.

Uses rustc, not the Rust seed as a product-test fallback. All build artifacts
live in a caller-selected directory outside the worktree.
"""
import argparse
from pathlib import Path
import subprocess

parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument("--rustc", default="rustc")
parser.add_argument("--output", type=Path, required=True)
args = parser.parse_args()
root = Path(__file__).resolve().parents[2]
args.output.mkdir(parents=True, exist_ok=True)
helper = root / "src/compiler_rust/common/src/atomic_update.rs"
exe = args.output / "atomic-update-check.exe"

owners = [
    ("compiler/src/interpreter_extern/sha256.rs", "let SHA256_COUNTER = AtomicI64::new(1);", "Ok(1)"),
    ("compiler/src/interpreter_state.rs", "let RECURSION_DEPTH = AtomicUsize::new(1);", "Ok(1)"),
    ("runtime/src/value/sffi/hash/sha256.rs", "let SHA256_COUNTER = AtomicI64::new(1);", "Ok(1)"),
    ("runtime/src/vulkan_graphics_runtime_core.rs", "let NEXT_HANDLE = AtomicI64::new(1);", "Ok(1)"),
    ("runtime/src/value/collections.rs", "let counter = &AtomicU32::new(1);", "Ok(1)"),
]
# Uppercase atomic names in the owners are statics. Use block-scoped statics
# in this isolated codeunit so all six actual call expressions typecheck.
source = 'extern crate self as simple_common;\n#[path = ' + repr(str(helper)).replace("'", '"').replace('\\', '/') + '] pub mod atomic_update;\n'
source += "#[test] fn actual_owner_calls() { use std::sync::atomic::{AtomicI64, AtomicU32, AtomicUsize, Ordering}; use Ordering as AtomicOrdering;\n"
count = 0
for owner, setup, expected in owners:
    text = (root / "src/compiler_rust" / owner).read_text()
    marker = "simple_common::atomic_update::update_"
    start = 0
    while (start := text.find(marker, start)) >= 0:
        opening = text.index("(", start)
        depth, end = 1, opening + 1
        while depth:
            depth += (text[end] == "(") - (text[end] == ")")
            end += 1
        declaration = setup.replace("let ", "static ") if "COUNTER" in setup or "DEPTH" in setup or "HANDLE" in setup else setup
        declaration = declaration.replace(" = AtomicI64", ": AtomicI64 = AtomicI64").replace(" = AtomicUsize", ": AtomicUsize = AtomicUsize") if declaration.startswith("static") else declaration
        source += "{ " + declaration + " assert_eq!(" + text[start:end] + ", " + expected + "); }\n"
        count += 1
        start = end
assert count == 6, f"expected six owner call expressions, found {count}"
source += "}\n"
harness = args.output / "atomic-owner-calls.rs"
harness.write_text(source)
subprocess.run([args.rustc, "--edition=2021", "--test", "-Dwarnings", str(harness), "-o", str(exe)], check=True)
subprocess.run([str(exe)], check=True)
print("PASS: atomic helper and six actual owner calls")
