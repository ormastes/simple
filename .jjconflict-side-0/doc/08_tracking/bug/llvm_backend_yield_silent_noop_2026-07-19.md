# LLVM backend silently no-ops Yield (silent wrong code, not an error)

- **Date:** 2026-07-19
- **Status:** open
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
