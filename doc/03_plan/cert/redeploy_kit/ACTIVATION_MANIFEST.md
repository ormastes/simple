# Redeploy-Kit Activation Manifest

Status board for the cert redeploy-kit (workflow `wf_055e4267-2f0`). It records
which pieces are **LANDED on main now** and which are **STAGED (frozen)** —
held in preserved lane worktree commits and NOT applied to main's active source
or test suite, because their fixes are compiled into the FROZEN deployed binary
`bin/release/x86_64-unknown-linux-gnu/simple` and only take effect after a
bootstrap rebuild + redeploy.

Landing a spec that fails/hangs on the frozen binary into the active suite is
prohibited, so every STAGED patch below waits here until a clean compiler is
redeployed. When that happens, apply each patch from the cited commit and run
its verification.

## Landed now (verified on the deployed binary)

| Piece | Files | Evidence |
|---|---|---|
| MC/DC lib + source-to-source instrumenter | `src/lib/nogc_sync_mut/mcdc.spl`, `src/lib/nogc_async_mut/mcdc.spl`, `scripts/check/cert/mcdc_instrument.spl`, `scripts/check/cert/sample_and_or.spl`, `src/lib/nogc_sync_mut/test/mcdc_auto_instrument_spec.spl` (from lane-1 commit `4120b38b841`) | `mcdc_spec` 2/2, `mcdc_report_spec` 3/3, `mcdc_auto_instrument_spec` 3/3 PASS on `$BIN`; instrumenter reports 100% (Covered a,b,c) on the adequate set and 66% (Uncovered: c) on a reduced set. |
| All redeploy-kit design docs | `doc/03_plan/cert/redeploy_kit/*.md` | Documentation only. |

Note on the MC/DC "was broken/hung" claim: on **current origin/main**
(`620fc04479e`) `std.mcdc` was already working — `mcdc_report_spec` PASSES 3/3
and `mcdc_spec` PASSES 2/2 with no hang and no timeout. The lane-1 changes are
therefore a **strict additive improvement** (they add the source-to-source
instrumenter + its passing spec and extend `mcdc.spl` with the decision-tree
registration API) with **no regression**, not a repair of a broken/hung module.
The lane's originating premise (analyze_mcdc=0 / `_find_independence_pair` hang /
2-min timeout) did not reproduce on current main and is recorded here for
honesty. Lane-1 branched from `6adff817`; `mcdc.spl` is byte-identical between
`6adff817` and `620fc04479e`, so lane-1's 6 files apply cleanly forward.

## Staged / frozen (apply after redeploy — do NOT land to active source or suite)

### Patch 1 — Type-checker fatal enablement, Phase A (arity + arg-type)
- **Lane commit:** `2335da48061` (worktree `.claude/worktrees/wf_055e4267-2f0-2`)
- **Frozen source:** `src/compiler/80.driver/driver.spl` — adds
  `run_typecheck_fatal_pass` gated on `SIMPLE_TYPECHECK_FATAL=1`, routing the HM
  inference engine's `TypeInferError`s into `ctx.errors`. Flag UNSET keeps the
  ~993-module build byte-for-byte identical.
- **Fixes:** tool-qualification failure mode TOR-FM-02 (silent-accept of
  arity-too-many / arity-too-few / arg-type-mismatch — the last is a memory-
  safety class).
- **Staged tests:** `test/cert/redeploy_pending/typecheck_fatal/` —
  `reject_arity_too_many.spl`, `reject_arity_too_few.spl`,
  `reject_arg_type_mismatch.spl` (Phase-A acceptance criteria);
  `reject_undefined_type_annotation.spl` (Phase B),
  `reject_nonexhaustive_match.spl` (Phase C) — kept for kit completeness, NOT
  Phase-A guarantees; plus `README.md`.
- **Verify post-redeploy:** for each Phase-A file,
  `SIMPLE_TYPECHECK_FATAL=1 bin/release/x86_64-unknown-linux-gnu/simple run <file>; echo exit=$?`
  → non-zero exit AND a `[typecheck] ...` diagnostic on stderr. With the flag
  unset, behavior is unchanged (historical silent-accept).
- **Design:** `doc/03_plan/cert/redeploy_kit/typecheck_fatal_enablement.md`;
  burndown `doc/03_plan/compiler/type_system/typecheck_burndown.md`.

### Patch 2 — Value-based array print + defect fixes (seed runtime / JIT)
- **Lane commit:** `529e890e65a` (worktree `.claude/worktrees/wf_055e4267-2f0-3`)
- **Frozen source:** `src/compiler_rust/runtime/src/value/sffi/io_print.rs` —
  value-based array printing (item 01). The other four defects live in the Rust
  seed runtime + cranelift JIT and also require the redeploy.
- **Fixes / expected vs frozen-binary actual:**
  | Defect | Expected stdout | Frozen-binary actual |
  |---|---|---|
  | `print_array_value_based` | `[1, 2, 3]` / `[[1, 2], [3]]` / `[]` | `<array@0x...>` x3 |
  | `closure_return_across_function_boundary` | `105` | `<invalid-heap:0x69>` |
  | `trait_default_method_inherited` | `Yo` / `Good day` | SEGFAULT (exit 139) |
  | `mixin_class_use` | `15` / `Alice` | `<value:0x...>` / `0.0` |
  | `mixin_struct_use` | `15` / `Alice` | `error` / `0` + stderr diag |
  | `nested_closure_capture` | `36` | `0` |
- **Staged tests:** `test/cert/redeploy_pending/` — the six `.spl` specs above +
  `README.md`.
- **Verify post-redeploy:** run each staged `.spl` on the redeployed binary and
  match the Expected-stdout column. Item 01 additionally has Rust unit tests
  that pass now: `cargo test -p simple-runtime --lib io_print`.
- **Design:** `doc/03_plan/cert/redeploy_kit/01_print_array_value_based.md`
  through `05_nested_closure_capture.md` + `README.md`.

### Patch 3 — class reference model (class-in-array `Index` read + object-handle)
- **Lane commit:** `5f52474c04d1` (worktree `.claude/worktrees/agent-ad78d112959250811`;
  amended once to embed this sha, so the integrating HEAD may carry a later sha —
  cherry-pick the worktree HEAD, whose content is identical to `5f52474c04d1`).
- **Depends on:** the ObjectStore class-reference model already on main
  (commit `19cd165d238`, "feat(interp-obj): class reference model in 70.backend
  HIR interpreter (#112)"): `Value.Object{class_name, handle}`, `objects.spl`
  `ObjectStore`, `env.store`, and store-routed field read/assign. Patch 3 is the
  remaining piece that model needs to actually exercise the array repro.
- **Frozen source:** `src/compiler/70.backend/backend/interpreter.spl` — adds the
  missing `case HirExprKind.Index(base, index)` read arm to `eval_expr` (Array +
  Int index, bounds-checked). Returns the element verbatim; a CLASS element is a
  `Value.Object(handle)`, so reading it out of an array shares the one ObjectStore
  record (reference semantics fall out for free). Before this, `arr[0]` fell
  through to the catch-all `not_implemented`, so the class-in-array repro could
  not run under interpret mode (`CompileMode.Interpret` -> `InterpreterBackendImpl`,
  `driver_types.spl:52`). No other source file changes; struct/value paths untouched.
- **Fixes:** tasks #99(d) / #112 — interpret mode dropped mutations to a class
  instance read out of an array (printed `42`; default/JIT printed `777`). See
  `doc/08_tracking/bug/jit_class_mutation_drop_characterization_2026-07-04.md`.
- **Staged tests:** `test/cert/redeploy_pending/class_reference/` —
  `class_in_array_mutation.spl` (expect `777`), `shared_alias_mutation.spl`
  (`777`), `struct_value_copy.spl` (`42`), plus `README.md`.
- **Verify post-redeploy** (run against the redeployed self-hosted binary):
  1. `SIMPLE_EXECUTION_MODE=interpret bin/release/x86_64-unknown-linux-gnu/simple run test/cert/redeploy_pending/class_reference/class_in_array_mutation.spl` -> prints `777` (was `42`).
  2. `SIMPLE_EXECUTION_MODE=interpret bin/release/x86_64-unknown-linux-gnu/simple run test/cert/redeploy_pending/class_reference/shared_alias_mutation.spl` -> `777`.
  3. `bin/release/x86_64-unknown-linux-gnu/simple run test/cert/redeploy_pending/class_reference/struct_value_copy.spl` -> `42`.
  4. Re-run 1-2 under default `bin/simple run` (no env var) -> `777` (must stay correct; default/JIT already handled classes — this is the no-regression check).
  5. `bin/simple lint src/compiler/70.backend/backend/interpreter.spl` -> rc=0.
- **Honest scope / known adjacent gaps (NOT fixed here — do not treat as regressions):**
  - Struct field assignment is still unimplemented in the interpret-mode
    70.backend engine (field-assign routes only class `Object`s through the
    store); `struct_value_copy.spl` is therefore verified under DEFAULT mode.
    Tracked separately.
  - `Index`-as-assignment-target (`arr[i] = v`) and Dict/Tuple/string indexing
    are intentionally out of scope (`ponytail:` note in the arm); the repro needs
    only Array read.
  - The prior #112 lane also added ACTIVE-suite specs
    (`test/01_unit/compiler/interp_object_store_ref_model_spec.spl` and "Task 112"
    blocks in `test/03_system/interpreter/interp_value_semantics_b35_spec.spl`)
    that fail on the frozen binary; the coordinator should relocate them here or
    remove them from the active suite at integration (out of this lane's scope to
    rewrite another lane's committed tests).

## Why these are staged, not landed
`test/cert/redeploy_pending/**` is intentionally excluded from the normal test
suite (a perpetually-red gate is not the goal) and the frozen source patches
change compiled seed/compiler behavior that only materializes after a rebuild.
Landing either now would either break the active suite or ship dead source, so
they are held in the lane commits above and applied at redeploy time using this
manifest.
