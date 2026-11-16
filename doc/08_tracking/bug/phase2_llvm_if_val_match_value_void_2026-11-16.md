# Phase 2 LLVM backend: `if val ... else: match ...` used as a value lowers to void

Registered 2026-11-16. Status: open. Severity P2.

## Symptom

Frozen Phase 2 compiler (`/c/dev/p3diag/p2.exe`, pin `18a1f28937c2`), LLVM
backend, codegen error:

```
unsupported LLVM value conversion from i64 to void function=...FileFiberTldrBridgeV1._drain_completions value=%l182 at src/compiler/80.driver/driver_build/file_fiber_tldr_bridge_v1.spl:329:16
```

## Source location

`FileFiberTldrBridgeV1._drain_completions` in
`src/compiler/80.driver/driver_build/file_fiber_tldr_bridge_v1.spl` (at
`origin/release/1.0.0` 115bd321a44, the `val completion = if val retained =
self.pending_completion:` binding, about lines 306-321). Shape:

```
val completion = if val retained = self.pending_completion:
    retained
else:
    val taken_completion: Result<RingCompletion<i64>?, SimpleRingError> = ...
    match taken_completion:
        case Err(error): return Err(...)
        case Ok(Some(value)):
            self.pending_completion = Some(value)
            value
        case Ok(_): return Ok(())
```

An `if val ... else:` used as a value whose else branch is a `match` where some
arms `return` and one arm yields a value. The merge value's type appears to be
lowered as `void` (the arms that `return` contribute a void/never type that
wins the join), then the `i64` value cannot be converted to it.

## Repro / reduction status

Not reduced. A 25-line candidate repro (a class with `pending: Cpl?` and a `me drain(n) -> Result<i64, text>` using `val completion = if val retained = self.pending: retained else: <match with return/yield arms>`) was written, but could not be compiled: `p2.exe native-build --backend llvm` was refused by the build memory guard ("1500 MiB of RAM/commit headroom free, below the 24576 MiB reserve (SIMPLE_BUILD_MEMORY_RESERVE_BYTES)") because a long build was running on the shared host, and `p2.exe compile` only supports `--format=smf`. The reserve was deliberately not lowered. Whether the minimal shape reproduces is therefore UNKNOWN, and the current seed was not tried. The only known failing instance is the full `_drain_completions` above.

## Workaround (build tree, NOT yet verified by codegen)

Use a `var completion_slot: RingCompletion<i64>? = self.pending_completion`,
then a statement-form `match` that assigns the slot or returns, then
`completion_slot.unwrap()`. This avoids the value-position `if val/else/match`.
It has not yet been confirmed through a codegen run.

## Proposed fix

When joining the value types of an if/match expression, ignore arms that end in
`return`/`break`/`continue` (diverging, type `never`) instead of letting their
void type unify with the value arms. Add a regression spec for a value-position
`if val ... else:` whose else is a `match` with mixed returning and yielding
arms, run under the LLVM backend.

## Status

Open. Compiler code not changed by this registration.
