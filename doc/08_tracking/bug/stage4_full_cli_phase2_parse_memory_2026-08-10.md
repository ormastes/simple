# Stage 4 full CLI phase-2 parse memory kill

Status: open

## Reproduction

On Apple Silicon, use the deployed pure-Simple Stage 3 compiler to build
`src/app/cli/main.spl` with the canonical Stage 4 arguments: LLVM,
`core-c-bootstrap`, `--entry-closure`, `--low-memory`, one thread, streaming
surfaces, and the admitted bootstrap runtime archives.

The 2026-08-10 run discovered 2,037 modules in about 910 seconds. Phase 2 then
released parsed surfaces through sequence 300, reached roughly 1.7 GiB RSS at
100% CPU, and was killed with exit 137. No compiler diagnostic was emitted and
no full CLI artifact was produced.

## Impact

Current main's attested ARM64 QEMU producer invokes the full CLI `os` command.
The deployed Stage 3 artifact is compiler-only, so QEMU verification cannot
continue until either the full CLI fits the low-memory Stage 4 build or the
producer owns an equally strict Stage 3 native-build interface.

## Required fix

Profile retained phase-2 state and the unexpectedly broad CLI entry closure.
Preserve the existing source fingerprint, compiler receipt, no-stub policy,
cache identity, and immutable post-build checks. Do not fall back to the Rust
seed and do not weaken the attested QEMU producer.
