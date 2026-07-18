# Fresh-seed native-build stalls before cache/object creation

Date: 2026-07-18
Status: OPEN
Priority: P0 bootstrap blocker

## Symptom

The current Rust bootstrap seed accepts the full-source `native-build` command
but makes no externally visible compilation progress before a 900-second hard
timeout. It creates no output binary and leaves a dedicated fresh cache at zero
bytes.

The complete log contains only:

1. dynamic runtime-provider initialization rejected a directory path and fell
   back to the static provider;
2. the memory guard warned that `SIMPLE_LIB=src` contains more than 600 Simple
   files.

## Bounded reproduction

The same result occurred once with `--runtime-bundle simple-core` and once with
the bootstrap script's canonical `--runtime-bundle core-c-bootstrap`. Both used
the current rebuilt seed, LLVM, full compiler/app/lib sources, entry closure,
one worker, a fresh cache, strict no-stub mode, and
`src/app/cli/bootstrap_main.spl`. Each was killed by `timeout 900` with exit
124. No third attempt was made.

## Classification

This happens before the native-project cache or object-emission boundary, so it
does not admit or reject the new LLVM per-function-section implementation. It
is also distinct from the prior final-link unresolved-symbol frontier.

## Required solution and prevention evidence

Trace the bootstrap dispatch/startup path through runtime-provider selection,
entry-closure source collection, and the memory guard. The owner must either:

- reach a named compilation phase and create its first cache/object within a
  bounded startup budget; or
- fail fast with a specific configuration/error message.

Add one progress regression around that shared owner. The test must fail on a
silent pre-cache stall, terminate its child on deadline, and retain bounded
diagnostics. Then run one fresh bounded Stage 2. Do not mask the stall with a
longer timeout, another runtime alias, or permissive stubs.
