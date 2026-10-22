# MIR verifier TransferOut payload arity

Issue: https://github.com/ormastes/simple/issues/3022 (bug).

Status: source candidate; runtime qualification pending with the parent manual
affected-source replay owner. No compiler build, native build, or tests were run
in this source-only lane.

## Evidence and cause

Frozen revision: `aeb2517fac0a3f287aed4347d75235ac8976161d`.
The C06 compiler-driver manual affected-source replay reports
`enum pattern payload arity differs from declared variant` for
`src/compiler/50.mir/mir_verify.spl`. Evidence lives in
`build/native_probe/phase3-whole-20261011-c06/manual-affected-source-objects-c36-reviewed-fixes/compiler-driver/`
(`hir-fatal-groups.json` and `build.log`) under the C06 worktree.

`mir_instruction_kinds.spl` declares six TransferOut payloads: destination local,
source local, execution domain, mode, payload kind, and `runtime_classify: bool`.
The verifier's `visit_inst` arm matched only five. This is an actual consumer
shape mismatch, unlike the separate imported-type registration failures in the
same replay.

## Correction and regression

The arm now explicitly ignores all four metadata fields after the two locals.
It continues defining the destination and using the source. No enum declarations,
strict HIR arity checks, diagnostic levels, or ownership semantics change.

The existing `mir_verify_cfg_layout_spec.spl` adds cases for `runtime_classify`
false and true: a valid transfer defines its result, an undeclared source emits
MIRV-005b, and an undeclared destination emits MIRV-005b. The source-missing case
also checks that the valid destination does not produce MIRV-005e.

Pending qualification: strict HIR affected-source replay of `mir_verify.spl`
and the focused `mir_verify_cfg_layout_spec.spl` scenarios using the assigned
qualified runtime. Passing source inspection is not runtime evidence.
