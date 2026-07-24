# Stage-4 surface release marker order failure

## Status

Open. The live slope gate reaches the streaming marker parser but stops with
`release markers must be ordered`.

## Reproduction

Run `scripts/check/check-stage4-selfhost-module-release-slope.shs --live` around
the low-memory, entry-closure Stage-4 build of `src/app/cli/main.spl` using
`build/stage4-streaming-stage3/simple`.

Required activation:

- `SIMPLE_BOOTSTRAP_STAGE4=1`
- `SIMPLE_NATIVE_BUILD_ENTRY_CLOSURE=1`
- mode `aot`
- low-memory `1`
- backend `cranelift`

## Evidence

- Stage-3 compiler build: 674 compiled, 0 failed.
- Stage-3 canonical candidate frontend smoke: PASS.
- Checker activation: enabled.
- Final diagnostic: `release markers must be ordered`.
- No Stage-4 binary or bounded-slope PASS was produced.

Earlier failures in the same bounded cycle were a wrong bootstrap entry and
self-hosted generic `Result` method dispatch. Both were corrected before this
failure.

## Next step

Capture the rejected marker and its expected sequence in the checker diagnostic
without changing acceptance semantics, then determine whether the producer
emits a malformed/interleaved line or restarts its sequence during worker
handoff. Do not repeat the live build until that diagnostic is available.
