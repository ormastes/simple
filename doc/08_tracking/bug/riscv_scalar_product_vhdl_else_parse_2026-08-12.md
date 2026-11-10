# Seed parser rejects the RISC-V scalar-product VHDL renderer at `else:`

Date: 2026-08-12
Status: FIXED (2026-11-11, lane boot13 — parse gap verified closed at tip; the
formal-verification spec now compiles past the seed parser and its modules, and
its full run is tracked separately below)
Severity: high — blocks the formal-verification system spec before examples run.

## Symptom

```
bin/simple test test/03_system/compiler/formal_verification_2_0_spec.spl --mode=interpreter
```

fails during compilation with:

```
error: compile failed: parse: in
".../src/compiler/70.backend/backend/riscv_scalar_product_to_vhdl.spl":
Unexpected token: expected expression, found Else
```

The runner then reports zero examples executed and a `parse-error` verdict.

## Investigation

The source was reduced from a nested expression-level `else:` branch to an
explicit statement-level LSU branch, while preserving the rejection and success
paths. The same seed-parser diagnostic remained after the focused rerun. The
diagnostic has no source location, so a further parser change would be blind.

The `bin/simple` resolved for this run is the bootstrap seed at
`bin/release/x86_64-unknown-linux-gnu/simple`, which itself warns it is not the
normal self-hosted tool.

## Unblock condition

Make the parser report the source location for this `Else` token and align the
seed and self-hosted grammars for the applicable conditional form. Then rerun
the formal-verification spec and require at least one executed example.


## Resolution (2026-11-05, work branch work/libbug-linux-vhdlparse-20261105)

Root cause: seed-parser grammar gap, in TWO shared paths —

1. Expression form (`parse_if_expr` in
   `src/compiler_rust/parser/src/expressions/helpers.rs`): the block-form
   then-branch loop only terminated on `Dedent`/`EOF`, so a then-arm that
   started on the line after the colon and had `else:`/`elif` trailing on the
   arm's own line (no `Dedent` in between) was fed to `parse_item` and failed
   with "expected expression, found Else".
2. Statement form (`parse_block_body` in
   `src/compiler_rust/parser/src/parser_impl/core.rs`): identical loop
   limitation for `if cond:\n    stmt else: stmt`.

Fix: both loops now also break on `Else`/`Elif`; the if-chain readers
(`parse_if_expr`, statement `parse_if`/`parse_if_suspend`) close the
still-open arm `Indent` via the `Dedent` that trails the chain's final arm
(tracked by a new `Parser::block_body_ended_on_else` flag and, for the
expression form, a `then_arm_indent_unclosed` local). This aligns the seed
with the self-hosted grammar, which has always accepted both forms.

Diagnostic location: `ParseError::UnexpectedToken`'s `Display` now appends
`at line {L}, column {C}` from the span it already carried (the plain
display previously dropped it, which is why the report had no location).

Regression lock: `src/compiler_rust/parser/src/if_expr_newline_arm_trailing_else_test.rs`
(12 tests: both forms, elif chains, multi-unclosed-indent chains, sibling
statement / fn-end neighbours, stray-else still rejected, block-form
controls). Verified: `cargo test -p simple-parser` — 438 lib tests pass
(1 pre-existing unrelated failure in `tests/error_recovery_test.rs::
test_python_def_detection`, fails identically on the clean branch).

Note: 2026-10-11 commit a7c39dc8f5d reformatted every `src/` instance to the
block form as a workaround; with this parser fix that restriction no longer
applies to the seed.

## 2026-11-11 — lane boot13 (work/p3-boot13-20261111)

Status: **FIXED** (this row's parse defect). Verified at tip c8b6d0ebe90e with the
fresh seed (build-commit 46fe8f6b6def, seedfix A+B), seed-smoke runs:

- The seed grammar fix from the 2026-11-05 resolution is present in source
  (`block_body_ended_on_else` at
  `src/compiler_rust/parser/src/parser_impl/core.rs:123,209,310,1473`;
  `then_arm_indent_unclosed` at
  `src/compiler_rust/parser/src/expressions/helpers.rs:213,297,469`) and in the
  deployed seed binary: `bin/simple.exe test
  test/03_system/compiler/formal_verification_2_0_spec.spl --mode=interpreter
  --no-cache` now compiles the spec PAST parsing into semantic analysis — the
  `Unexpected token: expected expression, found Else` failure against
  `src/compiler/70.backend/backend/riscv_scalar_product_to_vhdl.spl` is gone.
- Seed-run gap found while executing the doc's unblock condition: two FV2
  evidence modules declared their public surface without `pub`, which the seed
  enforces strictly (fn-by-fn, first error wins):
  1. `compiler.mir_opt.dce_translation_validation` — `private fn dce_tv_optimize
     ... not visible` (also broke
     `test/01_unit/compiler/mir/dce_translation_validation_spec.spl` and both
     sibling DCE specs).
  2. `compiler.mir_opt.result_abi_translation_validation` — `private fn
     validate_result_abi_translation_v1 ... not visible`.
  Fixed in this lane by marking the consumed surface `pub` in both modules
  (`pub enum`/`pub struct`/`pub fn`, leaving the underscore-prefixed internal
  helpers private). Pairwise verification (seed-smoke, all previously RED with
  the same visibility error):
  - `test/01_unit/compiler/mir/dce_translation_validation_spec.spl` — 3/3 PASS
  - `test/01_unit/compiler/mir/dce_translation_validation_linear_spec.spl` — 3/3 PASS
  - `test/01_unit/compiler/mir/dce_mir_translation_validation_spec.spl` — 9/9 PASS
- Residual blocker (routed, not re-diagnosed): after those fixes the
  formal-verification spec's 81 examples still do not execute because compilation
  stops at the known live `VirtMemManager` tri-definition ambiguity
  (`src/os/kernel/arch/x86_64/paging.spl` vs `memory/vmm.spl` vs
  `memory/vmm_core.spl`) — a separately tracked live defect outside this row.
  This row's tracked defect (the seed parser rejecting the renderer at `else:`)
  is closed: the renderer parses under the seed and the diagnostic-location fix
  stands. Full-run closure requires the VirtMemManager tri-def lane plus a
  follow-on visibility audit of the remaining FV2/verification import surface
  (candidate modules observed from the spec's import list; the seed reports one
  visibility error at a time, so this lane fixed only compiler-confirmed ones
  within its cycle budget).
