# `SIMPLE_COMPILER_PHASE_PROFILE=1` breaks any build: calls `rt_heap_registry_count`, which the seed lacks

- **Date:** 2026-07-20
- **Status:** open
- **Severity:** medium (the flag is a primary diagnostic for slow builds, and it
  fails the build outright instead of degrading)
- **Area:** `src/compiler/80.driver/driver_log_helpers.spl:9,46`

> **CORRECTION (same day).** This doc first claimed the failure was triggered by
> `SIMPLE_COMPILER_PHASE_PROFILE=1` and that builds without the flag proceed
> normally. **That is wrong** — a subsequent build with the flag removed failed
> identically. The title is kept for continuity; the real scope is broader and
> worse, as described below.

## Symptom

**Every** `native-build` against pristine compiler sources dies early with:

```
error: semantic: unknown extern function: rt_heap_registry_count
```

This is **not** flag-dependent. Verified: a build with
`SIMPLE_COMPILER_PHASE_PROFILE=1` and an otherwise identical build **without**
it fail the same way at the same point.

## Mechanism

`driver_log_helpers.spl:9` declares `extern fn rt_heap_registry_count() -> i64`,
and `log_phase` (line 46) calls it inside a trace-gated branch:

```simple
pub fn log_phase(msg: text):
    if driver_phase_trace_enabled():
        eprint("[BOOTSTRAP-PHASE] +{_phase_elapsed_ms()}ms {msg} heap_registry={rt_heap_registry_count()}")
```

The runtime gate is irrelevant: `unknown extern function` is a **semantic**
diagnostic raised while compiling the module, so the mere presence of the
declaration/reference fails the build whether or not the branch ever executes.

The symbol is registered on the Rust side
(`src/compiler_rust/common/src/runtime_symbols.rs:271,370`) but is **absent from
every seed binary present on this machine**:

| seed binary | has symbol |
|---|---|
| `src/compiler_rust/target/bootstrap/simple` (Jul 20 02:54) | no |
| `src/compiler_rust/target/release/simple` (Jul 19 23:52) | no |
| `bin/release/x86_64-unknown-linux-gnu/simple` (Jul 19 14:21) | no |

This is the standard "extern additions need a bootstrap rebuild" trap
(`.claude/rules/bootstrap.md`): the `.spl` + Rust registration landed without a
seed rebuild, so the deployed seeds cannot resolve it.

## Severity: `native-build` is broken on pristine sources

Because the failure is unconditional, **no one can `native-build` from a clean
checkout with any seed binary on this machine.** Everything that still appears
to work is being built in a worktree whose `driver_log_helpers.spl` is **locally
modified** to remove the declaration (confirmed: `build/worktrees/perffix` has
the file modified with zero occurrences and builds fine; a pristine checkout of
the *same commit* fails instantly).

That divergence is the reason this went unnoticed, and it is a trap in its own
right: two trees at the same commit behave differently, so a "working" build
proves nothing about what the committed source does.

## Fix options

1. Rebuild and redeploy the seed so the registered symbol actually resolves
   (the standing rule for extern additions).
2. Make the diagnostic degrade instead of aborting — a heap-registry count
   inside a log line must not be able to fail compilation. Drop it from the
   message or route it through an already-resolvable symbol.

Option 2 is worth doing regardless of 1: a diagnostic that hard-fails the build
is a bad failure mode, and it costs a confusing detour every time the seed
drifts from the registered symbol table.

## Related

- `doc/08_tracking/bug/seed_emit_object_superlinear_hang_large_module_2026-07-20.md`
  — this flag was being used to instrument that hang, and cost a build cycle.
