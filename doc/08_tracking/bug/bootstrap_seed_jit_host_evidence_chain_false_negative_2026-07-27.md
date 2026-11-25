# Bootstrap-seed JIT host-evidence chain false negative
## Open 2026-09-16 — needs owner triage

Triage 2026-11-25 (P3 fleet, worktree wt-p3-bas, Windows x86_64):
environment-blocked here — the repro needs the linux-triple bootstrap repair
artifact `build/bootstrap/repair-full/x86_64-unknown-linux-gnu/simple`
(absent in this worktree) and qualification against the Rust seed is
forbidden by the entry itself. The open question is an owner decision:
whether a JIT-vs-interpreter divergence confined to the diagnostic runner
(`src/app/test/test_host_env.spl` classification) warrants production
severity once a fresh admitted pure-Simple compiler reproduces it. Left
open; no code change attempted.

Reviewed in the 2026-09-16 bug-ledger normalization pass; no resolution
evidence found in the body. This is bookkeeping, not verification.

- Status: open, diagnostic runner only
- Owner: compiler/bootstrap diagnostics
- Production impact: none claimed; the Rust seed is forbidden for normal
  qualification

## Reproduction

With `build/cpu-simd-engine2d-evidence/evidence.env` retaining a valid x86_64
AVX2 receipt, the bootstrap repair artifact's default `run` mode classifies the
x86 row as blocked:

```sh
build/bootstrap/repair-full/x86_64-unknown-linux-gnu/simple run \
  src/app/test/test_host_env.spl
```

The same artifact in interpreter mode classifies the row as `pass` and retains
the correct source path:

```sh
SIMPLE_EXECUTION_MODE=interpret \
  build/bootstrap/repair-full/x86_64-unknown-linux-gnu/simple run \
  src/app/test/test_host_env.spl
```

A minimal interpreter probe reads all 2,478 evidence bytes and returns
`host_x86_simd_evidence_passes(evidence) == true`. The focused interpreter
SSpec passes 13/13.

## Expected

JIT and interpreter modes return the same pure-classifier result for the exact
same retained text. Reproduce with a fresh admitted pure-Simple compiler before
assigning production severity; do not repair or qualify against the Rust seed.

