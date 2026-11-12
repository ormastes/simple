# Stage 2 native HIR cache selfcheck fails to decode its own entry (enum wire allocation)

**Status:** OPEN (observed 2026-11-12, aarch64, Linux; lane bootstrap-fable-8/9/10)
**Area:** compiler / HIR cache codec under pure-Simple native codegen

## Symptom

While the Stage 2 (pure-Simple, cranelift) compiler builds the admission
fixture `src/compiler/bootstrap_admission/stage2_module_path_naming.spl`:

```
[hir-cache] SELFCHECK FAILED module=<snapshot>/src/compiler/bootstrap_admission/stage2_module_path_naming.spl
  path=<same> reason=decode bytes=259591 cause=reader kind=malformed
  detail=enum wire enum allocation failed line=3569/19823 token=0; entry not stored
```

(`src/compiler/80.driver/driver_hir_cache.spl:764`). The build continues —
the selfcheck refuses to store the entry, so the module is lowered again by
the main build — but every module that trips it loses HIR cache reuse. The
same message appeared on runs 8, 9 and 10 for this fixture; it is not known
how many of the 1,634 Stage 2 closure modules trip it.

## Why it matters

Stage 3 and the Phase 2 matrix tool builds rely on the HIR cache for warm
reuse; a codec that cannot round-trip its own encoding on the native lane
silently turns every build cold. Decoding fails at a fixed line/token of a
259,591-byte entry, which points at a specific enum wire shape (an enum with
payload inside the HIR of this fixture) rather than I/O.

## Reproduce

Any Stage 2 native-build of the fixture logs the line, e.g. the
run-10 admission smoke: `stage2-sanity.env.frontend-failure.log` of
`build/bootstrap-fable-10` under the lane's pinned snapshot, or the direct
replay in this lane's probe script (`probe_fixtures.sh`).

## Unanswered

- Which HIR node at line 3569 of the encoded entry carries the enum whose
  wire payload cannot be allocated, and whether the seed-built encoder or the
  native decoder is wrong (compare the seed interpreter's decode of the same
  bytes).
- Whether the matrix's `hir-cache` hit counters (`[hir-cache] hits=… refused=…`)
  show the same refusal class across the closure.
