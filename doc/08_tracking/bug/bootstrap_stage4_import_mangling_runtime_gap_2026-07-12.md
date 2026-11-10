# Bootstrap Stage 4 imported-call and runtime gap
## Open 2026-09-16 — needs owner triage

Reviewed in the 2026-09-16 bug-ledger normalization pass; no resolution
evidence found in the body. This is bookkeeping, not verification.

The 2026-07-12 full bootstrap proves Stage 2 and Stage 3 succeed through the
pure-Simple compiler. Stage 4 then fails while linking the full CLI.

Two independent owner classes remain:

1. imported Simple calls such as `run_check` and `run_arch_check` are emitted
   bare although the compiled objects define module-qualified symbols;
2. the full compiler CLI needs capability-owned providers beyond core-C, such
   as `rt_array_concat`, `spl_dlsym`, and `spl_wffi_call_i64`.

The POSIX/macOS/BSD core-C owner now provides `rt_process_run_timeout` with the
canonical tagged tuple ABI, concurrent stdout/stderr capture, monotonic timeout,
and process-group cleanup. The Windows source path uses restricted inherited
stdio handles, suspended launch, and a kill-on-close Job Object for descendant
cleanup. Windows compile/native proof and strict LLVM/Cranelift execution remain
pending, so this closes source ownership only; POSIX parity is not Windows proof.

The duplicated `ffi_gen.specs/process_mod.spl` timeout entries and
`sffi_gen.templates/simple_sffi.h` still describe a legacy generated string ABI
and are not the production native call-lowering owner. They remain a separate
generator cleanup; production is locked by the four-register `runtime_sffi.rs`
contract and text/array expansion mapping.

TODO: reuse the existing unique bare-to-qualified alias analysis at the hosted
ELF linker boundary (or fix call-target mangling at its canonical owner), then
route remaining symbols through the exact Stage4 provider profile. Do not
select raw `native_all`, generate symbol stubs, add feature-local `rt_*` aliases,
or re-enable a hosted runtime bundle for ordinary applications.

## Verification (2026-07-17)

No single-file repro possible — this bug's scope is architecture-level full-CLI
linking, not an isolated function. Cross-referenced verification against
`doc/08_tracking/bug/native_build_stage4_pre_object_spin_2026-07-13.md`
(2026-07-16 entries):

- Sub-issue (a) — bare `run_check`/`run_arch_check` imported-call mangling:
  **FIXED-AT-TIP**. The Stage-4 entry doc explicitly notes that a recent change
  "removes an obsolete blanket exclusion" and "proves the owner fix for
  run_check and run_arch_check."

- Sub-issue (b) — capability-owned providers missing (`rt_array_concat`,
  `spl_dlsym`, `spl_wffi_call_i64`): **REMAINS OPEN**. Same doc's final
  2026-07-16 entries explicitly state "This boundary is intentionally not called
  from the production `link_llvm_native` body" and "Provider composition, TODO
  535" remains incomplete.

**Status:** PARTIALLY-FIXED. Sub-issue (a) resolved; sub-issue (b) remains
explicit open TODO per cross-referenced doc.

## 2026-11-10 status — P3 runtime-lane triage (worktree simple-p3-rt-20261110)

**Verdict: SUPERSEDED.** Sub-issue (a) (bare `run_check`/`run_arch_check`
mangling) stays FIXED-AT-TIP per the in-doc 2026-07-17 verification. Sub-issue
(b) (Stage-4 full-CLI capability providers) is no longer tracked here: the
current authority is the newer OPEN bug
`stage4_full_cli_unlinkable_579_unresolved_runtime_symbols_2026-09-01.md`
(2026-09-01), which tracks the same link boundary host-independently.

Source audit at base 1504212d788b — all three sub-issue-(b) symbols have live
runtime providers, so no `src/runtime` gap remains on this side of the
boundary:

- `rt_array_concat` — `src/runtime/runtime_native.c:11122`
- `spl_dlsym` — `src/runtime/runtime_native.c:11370` (also `runtime_dynload.c:2077`)
- `spl_wffi_call_i64` — `src/runtime/runtime_native.c:11421`

What remains is the Stage-4 linker/provider-composition boundary itself
(compiler/native_project lane, per the TODO's own "fix call-target mangling at
its canonical owner" note), which the 2026-09-01 bug tracks. No `src/runtime`
change made; nothing further actionable in this lane. Execution label:
host-independent-source (presence verified by source audit at a pinned base).


## Triage 2026-11-10 (p3-boot3 lane, assignment row 21)

**Verdict: SUPERSEDED — corroborated independently.**

The same-day runtime-lane triage above stands. Re-verified at this lane's
base (origin/release/1.0.0, worktree simple-p3-boot3-20261110):

- The superseding tracker
  `stage4_full_cli_unlinkable_579_unresolved_runtime_symbols_2026-09-01.md`
  exists.
- All three sub-issue-(b) providers are live at the cited lines:
  `rt_array_concat` `src/runtime/runtime_native.c:11122`,
  `spl_dlsym` `:11370`, `spl_wffi_call_i64` `:11421`. No `src/runtime` gap
  on this side of the Stage-4 link boundary.

No change made in this lane; the Stage-4 linker/provider-composition boundary
remains with the compiler/native_project lane under the 2026-09-01 tracker.
