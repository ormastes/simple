# Standalone backend codegen check crashes deployed compiler

Status: open; one observation, no retry under the runaway guard.

## Observation

During static verification of the aspect/facet MIR exception-CFG production
gate, the deployed self-hosted compiler successfully checked the focused MIR
exception files and specs, but a standalone check of
`src/compiler/70.backend/codegen.spl` terminated with `SIGSEGV`.

The failing command was not retried. No seed-compiler fallback was used.

## Expected

Checking the backend codegen owner should either succeed or return a stable
compiler diagnostic. It must not terminate the compiler process.

## Impact

- The new codegen choke-point integration lacks admitted standalone executable
  evidence.
- Full compiler/backend verification and release remain blocked.
- The passing focused MIR checks do not prove the backend aggregate compiles.

## Follow-up

Reproduce in a fresh scoped session with the pure-Simple release binary, capture
the first failing stack/source location, fix the self-hosted compiler or the
codegen source, and run the standalone check once after the fix. Do not loop or
fall back to the Rust seed.
