# Formal Codegen Semantic-Preservation Plan (DO-333)

Status: **planning** (Phase 6 gap in `cert_roadmap.md`). Companion to `svp.md` §Formal
verification.

## Audit finding

The 27 zero-`sorry` Lake projects under `src/verification/` (gated by
`scripts/check/check-lean-proofs.shs`, auto-discovered via
`find "$VDIR" -maxdepth 3 -name 'lakefile.toml' -o -name 'lakefile.lean'`) model:

- concurrency/runtime soundness: `actor_channel`, `kernel_scheduler`, `thread_lifecycle`,
  `process_lifecycle`, `async_compile`, `tls_isolation`
- memory/borrow soundness: `gc_boundary`, `gc_manual_borrow`, `gc_reachability`,
  `manual_pointer_borrow`, `memory_model_drf`, `memory_capabilities`
- storage/filesystem invariants: `db_storage`, `fat32`
- type/module-system soundness: `type_inference_compile`, `type_value_semantics`,
  `module_resolution`, `visibility_export`, `macro_auto_import`, `tensor_dimensions`
- other model-checker-rule domains: `aop_weaver`, `ffi_contract`, `ui_compositor`,
  `kernel_capabilities`, `riscv_product`, `nogc_compile`, plus `formal/nvfs`

**None model HIR→MIR→codegen lowering or translation correctness.** There is zero formal
coverage of "does the compiler preserve program semantics when it lowers and optimizes,"
which is exactly the DO-333 codegen-correctness question and the thing the stage4 wall
incident (seed cranelift mis-lowering the ANY-erased `Dict<text,Value>` enum-payload
channel) demonstrates matters in practice.

## (a) Approach: translation validation, not whole-compiler refinement

Two candidate strategies:

1. **CompCert-style whole-compiler refinement proof** — prove once, for all inputs, that
   `⟦lower(p)⟧ = ⟦p⟧` for the entire HIR→MIR→backend pipeline. Rejected as the *first*
   step: the backend targets multiple ISAs (x86_64, arm64, riscv) plus an interpreter
   path, and formalizing that whole surface is a multi-year effort disproportionate to
   the current 27-project scale of the verification tree.
2. **Per-compile translation validation (TV)** — for each individual compilation, run a
   fast checker that proves *this specific* lowering/optimization step preserved
   semantics, re-run every compile. **Chosen.** Rationale: (i) tractable at the current
   verification-tree scale — one narrow theorem per rewrite class, matching the existing
   per-property Lake-project pattern (e.g. `actor_channel`, `db_storage`: one focused
   soundness claim each, not a whole-system model); (ii) matches the existing
   "generated-constraint" pattern already used by the Lean tree, where each project
   proves a specific generated obligation rather than a universal theorem over the whole
   compiler; (iii) avoids formalizing the full multi-ISA backend and the interpreter
   fallback path, which TV does not require (TV only checks the rewrite actually
   performed, not all rewrites the compiler could perform).

## (b) Minimal first proof: `src/verification/mir_opt_tv/`

New Lake project, following the existing per-property project shape (see
`src/verification/actor_channel/lakefile.toml` for the template: `name`,
`defaultTargets`, one `[[lean_lib]]`).

- **Target lowering:** the constant-fold + copy-propagation rewrite in
  `src/compiler/60.mir_opt` (MIR→MIR, the simplest optimization in the pipeline — no
  register allocation, no ISA selection, no multi-block CFG restructuring beyond basic
  copy/constant substitution).
- **Theorem:** `validate_sound` — for a MIR function `f` and its rewritten form
  `f' = const_fold_copy_prop(f)`, every well-typed input environment `env` yields
  `eval(f, env) = eval(f', env)` (or both diverge/error identically), where `eval` is a
  small-step MIR interpreter defined *only* over the constant-fold/copy-prop-relevant
  instruction subset (loads, stores, arithmetic, moves, conditional branch on a constant-
  foldable condition) — not the full MIR instruction set.
- **Acceptance criteria:**
  1. `lake build` succeeds with zero `sorry`/`admit`/`axiom`/`opaque` (enforced
     automatically by `check-lean-proofs.shs`'s `TRUST_RE` — no script change needed,
     auto-discovery already walks `src/verification` to depth 3).
  2. `validate_sound` is stated over an explicit, finite instruction-subset datatype (not
     an informal comment) so the theorem's scope is machine-checkable, not just asserted.
  3. At least one adversarial counter-example rewrite (a *deliberately unsound* fold, e.g.
     folding across a side-effecting call) is included as a *disproved* lemma
     (`example : ¬ validate_sound bad_rewrite := ...`) to demonstrate the theorem is not
     vacuously true.
- **Explicit OUT-OF-SCOPE for this first proof** (deferred to the follow-on sequence
  below, not silently assumed sound):
  - register allocation (`src/compiler/70.backend` register-assignment passes)
  - multi-ISA backend code generation (x86_64/arm64/riscv instruction selection/emission)
  - the full MIR instruction set (only the constant-fold/copy-prop-relevant subset above)
  - the interpreter execution path (`src/compiler/95.interp`) — TV here only concerns the
    compiled-code lowering, not interpretation semantics

## Integration

- No change needed to `scripts/check/check-lean-proofs.shs`: its auto-discovery loop
  (`find "$VDIR" -maxdepth 3 ... -not -path '*/.lake/*'`) picks up any new
  `lakefile.toml`/`lakefile.lean` automatically, and `TRUST_RE` already bans the same
  trust-bypass patterns project-wide. Dropping `src/verification/mir_opt_tv/lakefile.toml`
  in place is sufficient; it appears in the PASS/FAIL table as
  `verification/mir_opt_tv` on the next run.

## Follow-on sequence (after `mir_opt_tv` lands)

1. Extend `mir_opt_tv`'s instruction subset to cover dead-code elimination and common
   subexpression elimination (the next two passes in `60.mir_opt`), reusing the same
   `eval`/`validate_sound` scaffold.
2. Add a TV project for one register-allocation invariant (e.g. "no two live ranges that
   interfere are assigned the same physical register") — narrower than full regalloc
   correctness, but the first concrete backend-adjacent proof.
3. Add a per-ISA TV project for the simplest backend (start with the pure-Simple
   interpreter-adjacent codegen used by `bin/simple`, per the "clean backend" evidence in
   `redeploy_selfhost_plan.md`, before x86_64/arm64/riscv).
4. Wire a `--emit-tv-obligation` flag on the compiler so TV runs automatically as part of
   `bin/simple build check` on a representative corpus, not just as a standalone proof of
   one hand-picked rewrite.
5. Re-assess: once 2–3 passes + one backend have TV coverage, revisit whether a
   CompCert-style whole-pipeline refinement proof becomes tractable, or whether TV
   remains the permanent strategy (likely, given the multi-ISA/self-hosted-interpreter
   surface).
