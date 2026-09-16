# Self-hosted native build has no usable liveness trace or parallel compilation

## Evidence

The bounded V9 self-hosted compiler build invoked the pure-Simple release
binary with `SIMPLE_COMPILER_TRACE=1`, `SIMPLE_COMPILER_PHASE_PROFILE=1`, a
fresh cache, and a 120-second termination bound. Its log contained only the
global co-compilation warnings; it did not contain a native phase marker,
module-progress record, or `phase.marker` cache artifact.

The build worker runs the compiler graph through interpreted Simple before
native code generation. Earlier evidence records this path as tens of minutes
or longer. The current `ParallelBuilder` chunk loop also invokes its compile
function serially, so `--threads 8` is not evidence of concurrent progress.

## Required remediation

1. Emit stable phase and module progress records from the worker before and
   during source loading, frontend/MIR work, code generation, linking, and
   cache writes whenever the trace/profile environment flags are enabled.
2. Write a cache phase marker before entering each expensive phase, with the
   module count and last completed module.
3. Either implement bounded worker parallelism in `ParallelBuilder` or reject
   misleading thread counts until compilation is genuinely concurrent.
4. Add a bounded integration check that observes a phase transition without
   requiring the complete self-hosted build to finish.

## Progress

The parent native-build launcher now appends `native-build:worker-launch` to
`SIMPLE_COMPILER_PHASE_PROFILE_FILE` immediately before spawning the worker.
A bounded ten-second probe retained that receipt even though the worker did
not complete. This distinguishes launcher failure from pre-driver worker time;
worker/frontend phase progression and actual parallel compilation remain open.

The trace now has two additional durable handoff points: the worker appends
`native-build:worker-enter` before argument decoding, and `cli_native_build`
appends `native-build:driver-enter` before option validation. These markers use
the inherited explicit sink rather than stderr, so the next bounded probe can
separate process startup/loading time from compiler entry and entry-closure
discovery. If a run still contains only `native-build:worker-launch`, the
worker did not reach its Simple entrypoint before termination (or the binary
did not execute the current worker source); it is not evidence that phase-2
parsing began.

### Entry-closure parser failure, reproduced 2026-08-13

A fresh-cache, 20-second entry-closure build now reaches the worker and exits
with a concrete parser failure before V9 lowering:

```
src/compiler/70.backend/backend/lean_backend.spl:
Unexpected token: expected pattern, found Indent
```

The same release executable accepts that file in isolated `simple check`
mode. This is therefore an entry-closure/parser-context defect, not evidence
that a local V9 source file is malformed. The failure must be isolated with a
minimal entry-closure reproduction before changing the concurrently-owned Lean
backend; no release qualification command should be represented as running
past this point.

### Parser-context correction, reproduced 2026-08-13

The sole multi-line `case A |` pattern in `lean_backend.spl` was collapsed to
the canonical one-line form. A fresh bounded entry-closure probe no longer
reports the Lean parser error: it remains alive until the 20-second timeout
while emitting only ordinary co-compilation warnings. This resolves the
immediate parser-context blocker. It does not establish a successful native
build: phase records still stop at `native-build:worker-launch`, so bounded
worker progress and throughput remain the active qualification blocker.

## Impact

V9's source-level and bootstrap evidence cannot become admitted production
qualification until the self-hosted runtime can be built and its progress is
observable. Re-running the same uninstrumented multi-minute command provides
no additional evidence.
