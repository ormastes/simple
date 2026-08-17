# LLVM backend silently no-ops Yield (silent wrong code, not an error)

- **Date:** 2026-07-19
- Status: OPEN (P3)
- Status re-verified 2026-08-17 by source inspection (triage shard 02).
- **Severity:** medium (no current in-tree consumer emits Yield through the
  LLVM path, but the failure mode is silent wrong code, not a diagnostic)
- **Area:** src/compiler_rust/compiler/src/codegen/llvm

## Symptom

A `gen fn` containing `yield` compiled through the LLVM backend produces a
function in which every `Yield` is dropped with no error, no warning, and no
runtime trap — the generator body runs as a plain function and yielded values
vanish.

## Evidence (source-confirmed, 2026-07-19 survey)

- `src/compiler_rust/compiler/src/codegen/llvm/functions.rs:1475` — `Yield`
  (with `ActorSend`/`ActorReply`) lowers to a literal empty block `{}`.
- Contrast: the Cranelift/JIT path has a real state-machine lowering
  (`codegen/instr/body.rs:542-1025`, `async_ops.rs:65-121`) via
  `rt_generator_*` externs, and native-build's compilability gate forces
  `FallbackReason::Generator` interpreter fallback (`compilability.rs:330,823`)
  — so the LLVM no-op is only reachable where that gate is bypassed, but when
  reached it is SILENT.
- Related open gaps: `doc/08_tracking/bug/async_await_interpreter_crashes_2026-06-11.md`
  (B3 history: JIT used to trap on yield; downgraded to nil-return),
  `std_async_runtime_native_backend_gaps_2026-06-11.md`.

## Expected

Either implement generator lowering on the LLVM path, or make `Yield` a HARD
compile error there ("generators unsupported on LLVM backend") so the failure
is loud. Silent-drop of a control-flow instruction is never acceptable.

## Context

Found during the wave-4 coroutine research
(`doc/01_research/hardware/nvme_fw_coroutine/embedded_coroutine_statemachine_research.md`),
which concluded `gen`/`yield` are unusable for baremetal firmware and adopted
explicit-state FSMs instead — this bug is why the research doc forbids citing
`gen`/`yield` as a working primitive anywhere AOT.

## 2026-08-17 re-verification (lane s2_rust_codegen) — CONFIRMED LIVE, still latent

Confirmed by reading current source, not by commit ancestry.

`src/compiler_rust/compiler/src/codegen/llvm/functions.rs:1662`:

```rust
MirInst::ActorSend { .. } | MirInst::ActorReply { .. } | MirInst::Yield { .. } => {}
```

Still an empty arm — a `Yield` reaching the LLVM backend emits no code at all and
raises no diagnostic. Note the deliberate contrast with the arm immediately above
it (`:1651-1660`), which at least inserts a default `0` into `vreg_map` for the
dest-carrying async/actor instructions; the `Yield` arm produces nothing.

**Why this stayed P3 and was not patched here:** no consumer currently emits
`MirInst::Yield`, so the no-op is latent — it cannot silently corrupt a result
today. That also makes it **unreproducible from a spec**: a reproducing spec is
impossible to write while nothing emits the instruction, and a spec that
"passes" without exercising the path would be vacuous. This lane therefore did
not fix it, rather than land a change it could not test.

**Recommended fix when a consumer lands:** split `Yield` out of this arm and make
it a hard `CompileError` ("LLVM backend: MirInst::Yield unsupported") rather than
a silent drop. Failing closed converts a future silent miscompile into a loud
one, matching how this backend already fails closed on unresolved method calls
(see `membership_query_untagged_key_llvm_backend_2026-08-02.md`). Whoever wires
the first `Yield` producer must land that arm in the same change.

### Could NOT prove
Nothing was executed. This is a source-inspection confirmation only. In
particular this lane did not verify the claim that no consumer emits `Yield` — it
carried that forward from the existing triage evidence and did not independently
sweep for producers.

## Content re-verification 2026-08-17 (m2_rust_compiler lane) — CONFIRMED STILL OPEN (latent)

`src/compiler_rust/compiler/src/codegen/llvm/functions.rs:1662` still reads
`MirInst::ActorSend { .. } | MirInst::ActorReply { .. } | MirInst::Yield { .. } => {}`
under the comment "Async instructions without dest vreg" — an empty arm, i.e. a
silent no-op for `Yield`. Unchanged from the original report.
