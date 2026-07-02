# SimpleOS LLVM Port Evidence Current - 2026-07-02

## Scope

Focused LLVM-to-SimpleOS port evidence for the current hardening lane.

## Results

| Gate | Status | Evidence |
| --- | --- | --- |
| Cross-build plan scaffolding | PASS | `SIMPLE_LIB=src bin/simple test test/02_integration/os/port/llvm/cross_build_plan_spec.spl --mode=interpreter --clean` -> 15 examples, 0 failures |
| Per-target compiler-rt/build staging scaffolding | PASS | `SIMPLE_LIB=src bin/simple test test/02_integration/os/port/llvm/per_target_build_spec.spl --mode=interpreter --clean` -> 21 examples, 0 failures |
| Cross clang live smoke | FAIL | `SIMPLE_LIB=src bin/simple test test/02_integration/os/port/llvm/smoke_clang_spec.spl --mode=interpreter --clean` -> 5 examples, 1 failure |

## Current Blocker

`smoke_clang_spec.spl` still resolves the clang smoke to the host toolchain path
and reports `x86_64-pc-linux-gnu` from `clang --print-target-triple` instead of
`x86_64-simpleos`. The live smoke remains blocked until `LLVM_BUILD` points at a
real SimpleOS cross LLVM build, or the interpreter env handoff is fixed so the
unset `LLVM_BUILD` path reliably skips.

## Spec Maintenance Completed

- Updated stale `fs.read_to_text` usage to current process-backed file reads for
  the static specs.
- Updated stale direct bool matcher calls to `expect(...).to_equal(true)` via a
  local `check` helper.
- Updated the static target assertions to include the current
  `armv7-unknown-simpleos` target.
- Updated process result checks to the current `ProcessResult` fields.
