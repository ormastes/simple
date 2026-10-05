# Full subsystem tests were not the diagnostic smoke binaries

Source examined: `e37658577b3279e30f1631dfcc8474d1c860511b`.
Status: investigation; full products remain unbuilt and unqualified.

## Actual executed scope

`diagnostic-authored-tests-p23bd20-1` intentionally selected three unchanged
authored-main smoke programs: boolean representation (7 checks), enum numeric
payload widths (13), and array mutation (20). Each ran on Cranelift and LLVM.
All six diagnostic binaries linked and executed: 80 checks, 38 passed, 42 failed.
These are not the compiler, interpreter, and loader aggregate products.
Three other direct fixtures containing 38 checks remained explicitly excluded;
their checks are neither executed nor passed. The earlier typed-I/O 8-check
result is separate and was not rerun.

## Full-product discovery inventory

The tracked HEAD source selection in
`scripts/bootstrap/compiler-subsystem-test-inventory.shs` includes these files:

| Owner | Unit files | Integration files | System files | Total files |
|---|---:|---:|---:|---:|
| compiler | 2915 | 185 | 554 | 3654 |
| interpreter | 158 | 4 | 25 | 187 |
| loader | 237 | 1 | 0 | 238 |
| Total | 3310 | 190 | 579 | 4079 |

These are tracked source-file counts, not parsed test cases, registered cases,
executed checks, or proof that every selected file can compile. The canonical
script's separate physical-inventory verification completed successfully and
matched all 4079 tracked owners, recording a content digest for every file in
`full-subsystem-source-inventory-e376.tsv`. This verifies materialization and
file inventory, not test registration or execution.

The current rule accepts only `test/01_unit`, `test/02_integration`, and
`test/03_system`, with owner-directory matching and `_spec.spl`/`_test.spl`
suffixes. A second tracked-tree audit found 1446 additional ownership-matching
spec files outside that rule. Of these, 23 are formal-verification files and 15
are performance files; the other 1408 are in legacy/other locations, including
1159 under `test/unit/compiler`, 109 under `test/unit/compiler_core`, 28 under
`test/integration/compiler`, and 50 under `test/system/compiler`.
They require a migration/duplicate/eligibility audit before claiming whole-suite
coverage. Do not silently omit them or simply sum them as distinct test cases.

## Why the full products were not built

Both native prerequisite tools failed during MIR lowering:
`compiler_subsystem_product_generator` and `compiler_subsystem_main_verdict`.
Errors include duplicate imported-global providers and unresolved methods in
shared process/environment code. Consequently no source-bound parser span and
verdict ledgers were available for the existing aggregate renderer. The product
runner also requires a separately admitted generated source root; it explicitly
rejects writing generated code into the frozen source checkout.

The retained-HIR retry, `test-builders-p23bd-retained20-1`, disabled streaming
surfaces while keeping the same compiler and source. Duplicate-provider errors
disappeared, but the generator still reported 25 MIR errors and the verdict tool
17. Both exited 1; neither produced a full-product binary. This is evidence for
separate transport and receiver/provider defects, not a passing workaround.

The reviewed helper repair chain is published through `9da30fdf224` on
`work/helper-provider-blockers-20261005`. It preserves concrete optional-text
and process receiver types, admits struct-only method providers, and requires
the exact qualified declaration owner. Regression fixtures include rejected
wrong-owner methods. The same chain is applied through `f9b2b30e8fa` in the
separate full-bootstrap test-matrix worktree. Native verification is pending;
the running `102acf5d872` compiler candidate does not contain this chain.
Provider-lowering changes require a successor compiler before helper retries
can verify the repair. Existing running source roots remain frozen.

## Required completion evidence

Repair and verify the helper tools, audit the omitted legacy owners, admit the
generated source root, then build all three subsystem products for each backend.
Ask each real binary to enumerate its registry, reconcile that registry against
the source inventory and parser/verdict ledgers, and run it to completion.
Report registered, executed, passed, failed, skipped, and pending separately.
Neither source-file counts nor small smoke-test successes satisfy this gate.

Evidence packet root:
`C:/Users/user/.simple/worktrees/simple/runtime/windows-restart-20261004`.
Relevant artifacts: `subsystem-tracked-owner-counts.json`,
`subsystem-inventory-outside-scope.json`,
`diagnostic-authored-tests-p23bd20-1/results.json`, and
`test-builders-p23bd-hir20-1/results.json`.
