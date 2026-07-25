# Phase-profile tracing breaks every rv32 firmware build: `rt_heap_registry_count` missing from the seed

- **Date:** 2026-07-20
- **Status:** resolved 2026-07-24
- **Severity:** high (blocks **all** `fw_rv32` firmware builds on pristine
  sources — the scripts enable the triggering flag unconditionally)
- **Area:** `src/compiler/80.driver/driver_log_helpers.spl:9,45`

> **Revision history (read this before trusting an earlier revision).** v1 said
> the failure was gated by `SIMPLE_COMPILER_PHASE_PROFILE=1` — **correct**. v2
> "corrected" that to unconditional/semantic — **that was wrong**, and this
> revision retracts it. The v2 error came from testing via `build.shs`, which
> sets the flag itself (below), so removing it from my environment changed
> nothing and I misread the result as flag-independent. Isolated A/B on a
> two-line program now settles it.

## Symptom

```
error: semantic: unknown extern function: rt_heap_registry_count
```

## Isolated A/B (pristine `driver_log_helpers.spl`, two-line probe program)

| run | result |
|---|---|
| `native-build --target riscv32 --emit-object` | no extern error |
| same, with `SIMPLE_COMPILER_PHASE_PROFILE=1` | **`unknown extern function: rt_heap_registry_count`** |

So the failure **is** gated by the flag.

## Why it nonetheless breaks every firmware build

`examples/09_embedded/simpleos_nvme_fw/fw_rv32/build.shs` sets the flag itself
on **all three** `native-build` invocations — lines **241** (SMP), **437**, and
**531** (default):

```sh
$BUILD_RUNNER env SIMPLE_COMPILER_PHASE_PROFILE=1 SIMPLE_NATIVE_BUILD_EMIT_OBJECT=1 "$SIMPLE_BIN" native-build --backend llvm ...
```

Callers cannot opt out by unsetting the variable. So in practice **every
fw_rv32 build on pristine sources fails**, even though the underlying defect is
flag-gated. Both facts matter: the gate explains the mechanism, the scripts
explain the blast radius.

## Mechanism

`driver_log_helpers.spl:9` declares `extern fn rt_heap_registry_count() -> i64`;
`log_phase` (line 45) calls it inside the trace-gated branch:

```simple
pub fn log_phase(msg: text):
    if driver_phase_trace_enabled():
        eprint("[BOOTSTRAP-PHASE] +{_phase_elapsed_ms()}ms {msg} heap_registry={rt_heap_registry_count()}")
```

`driver_phase_trace_enabled()` is true for `SIMPLE_COMPILER_PHASE_PROFILE=1`
**or** `SIMPLE_COMPILER_TRACE=1` (line 13), so either variable triggers it.

The symbol is registered on the Rust side
(`src/compiler_rust/common/src/runtime_symbols.rs:271,370`) but is **absent from
every seed binary on this machine**:

| seed binary | has symbol |
|---|---|
| `src/compiler_rust/target/bootstrap/simple` (Jul 20 02:54) | no |
| `src/compiler_rust/target/release/simple` (Jul 19 23:52) | no |
| `bin/release/x86_64-unknown-linux-gnu/simple` (Jul 19 14:21) | no |

Standard "extern added without a seed rebuild" trap (`.claude/rules/bootstrap.md`).

## Why it stayed hidden

Worktrees used for this work have `driver_log_helpers.spl` **locally modified**
to drop the declaration (confirmed: `build/worktrees/perffix`, zero occurrences,
builds fine there). A pristine checkout of the *same commit* fails. Two trees at
one commit behaving differently is its own trap — a green build in a modified
tree proves nothing about committed source.

## Fix options

1. Rebuild and redeploy the seed so the registered symbol resolves (the standing
   rule for extern additions).
2. Make the diagnostic degrade rather than abort — a heap-registry count inside
   a log line must not be able to fail compilation.

Option 2 is worth doing regardless: a diagnostic that hard-fails the build it
exists to diagnose is a bad failure mode, and here it is wired on by default in
the firmware scripts, so it fails builds nobody asked to profile.

## Related

- `doc/08_tracking/bug/seed_emit_object_superlinear_hang_large_module_2026-07-20.md`

## Resolution (2026-07-24)

The runtime already exported `rt_heap_registry_count`, but the Rust
interpreter extern dispatcher did not register a handler for interpreted
compiler code. The dispatcher now forwards the call to the runtime and its
test registers a real temporary heap pointer, proving that the handler returns
the live registry count rather than a constant.

After rebuilding the Rust bootstrap binary, the full Stage 2 worker passed
this call and continued into parsing the 383-source closure. It next failed on
the separate interpreted-parser issue tracked in
`bootstrap_stage2_interpreted_parser_empty_array_2026-07-24.md`.
