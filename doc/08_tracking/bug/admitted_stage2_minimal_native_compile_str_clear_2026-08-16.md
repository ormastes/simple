# Admitted Stage2 minimal native compile fails at `str.clear`

## Triage 2026-11-10 (p3-boot lane)

SUPERSEDED — fix commit `3c31fc3aa8b6 fix(mir): route Dict.clear() to rt_dict_clear
instead of str.clear` (2026-08-17) is an ancestor of work/p3-boot-20261110
(`git merge-base --is-ancestor 3c31fc3aa8b HEAD` -> true).

Evidence in current tree:

- `src/compiler/50.mir/_MirLoweringExpr/method_calls_literals.spl:3336` —
  `is_dict_method_name` now includes `clear` (and `set`).
- `src/compiler/50.mir/_MirLoweringExpr/method_calls_literals.spl:4042-4057` —
  the `receiver_is_dict and method == "clear"` arm emits `rt_dict_clear`, with
  a comment naming this failure mode (`HirLowering.begin_module()`'s 15
  `Dict.clear()` calls being routed into `str.clear`'s
  `rt_refuse_non_text_receiver` guard, `src/runtime/runtime_native.c:7154`).
- In-tree regression spec: `test/01_unit/compiler/codegen/dict_clear_native_dispatch_spec.spl`
  plus probes `probe_dict_clear_native.spl` / `probe_nontext_receiver_dict_clear.spl`.
  Not re-executed here: the spec's oracle is a full native build of the probe,
  and the only driver available in this lane is the Rust seed (whose own MIR
  lowering compiled the probe), so a green run would not exercise the fixed
  self-hosted path and a red run would prove nothing about it. Commit ancestry
  plus the dispatch arm plus the pinned spec is the verification.

The runtime guard itself (`rt_refuse_non_text_receiver`) is intentionally loud
and unchanged — the repair was in dispatch, as this record's "Repair belongs
to the bootstrap/runtime owner" note anticipated.

Status: open runtime blocker for `compiler_minimal_native_compile_perf`.

An admitted Stage2 compiler at
`/mnt/data/worktrees/restart12-compiler_perf_a/build/restart12-build11-a-r4/output/stage3/x86_64-unknown-linux-gnu/stage2-admitted/simple`
with SHA-256
`68cbbbbd60ed073e2e21aac682207f0c21cef703f5fe7a920fee3e32c19af2aa`
was tried against three distinct minimal source shapes. Each bounded invocation
exited 70 in 0.01–0.04 seconds at roughly 9472–9728 KiB max RSS, emitted no
artifact, and reported `str.clear was called on a receiver that is not text`.

The failure occurs before a valid benchmark sample and therefore supplies no
baseline, optimization, or runtime PASS evidence. Source inspection localizes
the first minimal path to `HirLowering.begin_module()` clearing its diagnostic
collection before the stub-HIR boundary. Repair belongs to the bootstrap/runtime
owner, not this benchmark lane. Re-test only with a newly admitted pure-Simple
artifact and do not substitute the Rust seed.
