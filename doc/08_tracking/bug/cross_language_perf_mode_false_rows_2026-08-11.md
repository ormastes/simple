# Cross-language performance harness mode rows are not trustworthy
## Open 2026-09-16 — needs owner triage

Reviewed in the 2026-09-16 bug-ledger normalization pass; no resolution
evidence found in the body. This is bookkeeping, not verification.

## Status
Claimed for `compiler_loader_script_crosslang_perf`; no harness fix started.

## Evidence
The documented `simple run --mode=smf file` and `--mode=interpreter file` forms parse the mode token as a filename on the deployed binary. Placing the option after the source makes it a program argument, and the supposed interpreter, SMF, and native rows all follow the same JIT-to-interpreter fallback. The warm Fibonacci sources also discard their result, permitting dead-code elimination, and the harness omits Rust.

## Unblock condition
Bind each row to a proven execution mode, require an observable checksum, add Rust, fail closed on fallback, and rerun against an admitted self-hosted binary with matching warmups and CPU settings.

