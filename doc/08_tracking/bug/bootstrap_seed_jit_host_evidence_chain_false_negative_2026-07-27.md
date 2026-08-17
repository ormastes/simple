# Bootstrap-seed JIT host-evidence chain false negative

- Status: OPEN (P3)
- Status re-verified 2026-08-17 by source inspection (triage shard 00).
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
