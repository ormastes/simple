# `SIMPLE_COMPILER_PHASE_PROFILE=1` breaks any build: calls `rt_heap_registry_count`, which the seed lacks

- **Date:** 2026-07-20
- **Status:** open
- **Severity:** medium (the flag is a primary diagnostic for slow builds, and it
  fails the build outright instead of degrading)
- **Area:** `src/compiler/80.driver/driver_log_helpers.spl:9,46`

## Symptom

Any `native-build` run with `SIMPLE_COMPILER_PHASE_PROFILE=1` dies early with:

```
error: semantic: unknown extern function: rt_heap_registry_count
```

Without the flag, the identical build proceeds normally. The flag is therefore
**unusable with the current seed** — which is precisely backwards, since it
exists to diagnose builds that are too slow to finish.

## Mechanism

`driver_log_helpers.spl:9` declares `extern fn rt_heap_registry_count() -> i64`,
and `log_phase` (line 46) calls it inside the trace-gated branch:

```simple
pub fn log_phase(msg: text):
    if driver_phase_trace_enabled():
        eprint("[BOOTSTRAP-PHASE] +{_phase_elapsed_ms()}ms {msg} heap_registry={rt_heap_registry_count()}")
```

`driver_phase_trace_enabled()` is exactly the `SIMPLE_COMPILER_PHASE_PROFILE=1`
gate, so the extern is only reached when the flag is on. The symbol is
registered on the Rust side (`src/compiler_rust/common/src/runtime_symbols.rs:271,370`)
but is **absent from every seed binary present on this machine**:

| seed binary | has symbol |
|---|---|
| `src/compiler_rust/target/bootstrap/simple` (Jul 20 02:54) | no |
| `src/compiler_rust/target/release/simple` (Jul 19 23:52) | no |
| `bin/release/x86_64-unknown-linux-gnu/simple` (Jul 19 14:21) | no |

This is the standard "extern additions need a bootstrap rebuild" trap
(`.claude/rules/bootstrap.md`): the `.spl` + Rust registration landed without a
seed rebuild, so the deployed seeds cannot resolve it.

## Why it stayed hidden

Sessions that use this flag routinely work in worktrees where
`driver_log_helpers.spl` is **locally modified** to drop the call (confirmed:
`build/worktrees/perffix` has it modified with zero occurrences, and phase
markers print fine there). On pristine checked-out code the flag fails
immediately. Anyone comparing a "working" contaminated worktree against a clean
one will see two different behaviours from the same commit.

## Fix options

1. Rebuild and redeploy the seed so the registered symbol actually resolves
   (correct, matches the standing rule).
2. Make the diagnostic degrade instead of failing the build — the heap-registry
   count is a nice-to-have inside a log line and should not be able to abort
   compilation. Guard the call, or drop it from the message.

Option 2 is worth doing regardless of 1: a *diagnostic* flag that hard-fails the
build it is meant to diagnose is a bad failure mode, and it costs a confusing
detour every time the seed drifts.

## Related

- `doc/08_tracking/bug/seed_emit_object_superlinear_hang_large_module_2026-07-20.md`
  — this flag was being used to instrument that hang, and cost a build cycle.
