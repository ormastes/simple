# Stage-3 fold visitor passes an optional wrapper as HirType

Status: source repair prepared; executable qualification pending.

## Reproduction and owner

The rejected aarch64 candidate at
`/tmp/phase3-release100-j10-codec-ab5a444c7a1-20261023/stage2-rejected/aarch64-unknown-linux-gnu/simple`
fails the direct positional Stage-3 route in
`scripts/check/check-bootstrap-stage2-struct-receiver.shs`, compiling
`src/compiler/bootstrap_admission/stage2_module_path_naming.spl` with frontend
cache disabled. The crash occurs after HIR lowering, before MIR, through
`collect_module_representation_receipt_v1` and its actual-HIR observation pass.

A bounded GDB run against the existing executable copy
`/tmp/receiver-gdb-simple` stopped immediately before the failing call at
`0x797010` in `walk_hir_expr`. Its type argument was a boxed Option:

- Argument `x0 = x26 = 0x2f7fd21`.
- Box words: `0x1800000007`, `0xf198715900000001`, `0x2f7fd01`.
- Enum identity `1`, discriminant `0xf1987159`: `Some`.
- Caller expression-kind word `0x46cbfe9b04577129` has discriminant
  `0x46cbfe9b`: `ArrayLit`.

The deterministic DefaultHasher/SipHash-1-3 string discriminants were checked
independently for `Some` and `ArrayLit`. `addr2line` resolves function names
but reports no source lines for this candidate. The bounded run and memory
inspection are retained in `/tmp/hir-optional-edge-gdb.log`; the original
SIGSEGV backtrace is `/tmp/receiver-gdb.log`.

## Repair

`fold_gen._fold_lines` classified `HirType?` as a child node and directly passed
the optional wrapper to `walk_hir_type(HirType)`. A callee nil check cannot
unwrap a present Option. The generator now emits explicit `Some(payload)` /
`nil` matching at schema-declared optional node, list, and pair-list edges,
matching the existing read-only visitor generator's contract.

The representation pass and its unsafe-region diagnostics remain enabled.
Required child edges and the existing nullable-node behavior are unchanged.
The generated HIR and AST folds were manually synchronized because no usable
fullCLI interpreter is installed in this worktree. They were not regenerated.

The synchronized HIR edges are: `Expr.StringLit.interpolations`,
`ArrayLit.type_`, `ArrayRepeat.elem_type`, `DictLit.value_type`,
`SetLit.elem_type`, `If.else_`, `IfChain.else_`, `Return.value`, `Break.value`,
`Yield.value`, `EnumLit.payload`, `Range.start/end/step`, `TryCatch.finally_`,
`Pattern.Enum.payload`, and `AsmConstraint.output_value` (17 total).

The AST edges are: `Expr.StringLit.f1`, `Assign.f1`, `Range.f0/f1/f3`,
`If.f2`, `IfChain.f1`, `TryCatch.f2`, `Yield.f0`, `Return.f0`, `EnumLit.f2`;
`Stmt.Val.f1`, `Var.f1/f2`, `SharedVal.f2`, `SharedVar.f2`, `Assign.f1`,
`Return.f0`, `Yield.f0`; `Type.Array.f1`; `Pattern.Enum.f2`, `Range.f0/f1`;
and `AsmConstraint.output_value` (24 total).

## Evidence and remaining qualification

Static checks passed: exactly 17 HIR and 24 AST optional-edge wrappers;
removing only those wrappers restores each original generated file byte for
byte; generator optional dispatch precedes nonoptional child recursion.

`test/01_unit/compiler/schema/fold_optional_edges_spec.spl` adds generator to
generated-file equality for all eight changed walkers, absent and present
optional type traversal, nested collections, optional interpolation lists,
safe manifest receipts, and critical/moderate unsafe-region diagnostics.

These executable specs and generator freshness have **not run**. Both the
rejected candidate copy and the immutable Stage-2 reference expose the
bootstrap CLI and reject `run` as an unknown command. No Rust seed was used.
The GDB execution uses the unchanged rejected binary and proves the original
failure boundary, not success of the repair. A source-bound producer rebuild,
the focused spec, generator freshness, and the original direct Stage-3 route
must pass before this repair is qualified or the candidate is admitted.

## Release Phase3 recurrence — 2026-10-25

The canonical receiver gate built from source `f5c0f468556` with candidate
`11e78adecfa0c20917d41422e74a067a7409711b435ae3b2de2157f77ea541f0`
again passed the receiver compilation but crashed on the positional module-path
fixture after HIR. An ordinary GDB run on a byte-identical private executable
copy reproduced SIGSEGV in `walk_hir_type+192` (`0x799028`, `x8=1`), reached
from `walk_hir_expr`, `representation_observe_function_v1`, and
`run_representation_manifest_pass`. The rejected original was not modified.
Evidence: `/tmp/phase3-positional-receiver-diagnosis-20261025/ordinary-gdb-copy.log`;
explicit argv/environment and candidate hash are adjacent. GDB itself exits0
after reporting the signal; that is not a successful compiler result.

The three affected source beforeimages on this branch exactly match donor
`642659ae779763091e138b0226a7576fee435cc6`. This port reuses that generator,
generated HIR/AST folds and real regression SSpec without disabling the
representation pass. Focused rebuilt-producer qualification remains pending.
