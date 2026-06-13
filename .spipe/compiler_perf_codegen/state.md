# Feature: compiler_perf_codegen

## Raw Request
during harden simple os, harden simple compiler also in perf and code gen; small model-rated tasks, parallel agents, higher-model review after.

## Task Type
code-quality

## Refined Goal
Land 1-2 bounded, measured compiler perf wins in pure-Simple mir_opt/codegen and extend codegen correctness specs with riscv/arm64-sensitive cases mirroring existing x86 coverage.

## Acceptance Criteria
- AC-1: A shortlist (top 3) of bounded unlanded perf wins exists, sourced from doc/03_plan/compiler/perf and doc/03_plan/compiler/optimization.
- AC-2: At least one win is implemented in pure Simple (never the Rust seed) with before/after timing evidence recorded in the state file.
- AC-3: New codegen specs in test/01_unit/compiler/codegen/ cover at least 2 riscv/arm64-sensitive behaviors (e.g., cross-module ABI, baremetal module-level val) and pass.
- AC-4: bin/simple check is clean on every touched compiler file; existing codegen specs still pass in interpreter mode.

## Scope Exclusions
No Rust seed changes. No new backend targets. No changes outside src/compiler/** and test/01_unit/compiler/codegen/**.

## Phase
dev-done

## Log
- dev: Created state file with 4 acceptance criteria (type: code-quality)
