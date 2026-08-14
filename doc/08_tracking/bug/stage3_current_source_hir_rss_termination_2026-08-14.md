# Current-source Stage 3 terminates after unbounded HIR build RSS growth

- Status: OPEN
- Date: 2026-08-14
- Severity: P0 bootstrap blocker
- Owner: pure-Simple compiler/bootstrap memory lifecycle

## Reproduction

A single-writer, cache-preserving pure-Simple Stage-3 build used the
provenance-retained Stage-2 parent with LLVM, one worker, `dynload`, the
core-C-bootstrap runtime, and `SIMPLE_NO_STUB_FALLBACK=1`. After the HIR
contract model fix removed the prior Phase-3 unresolved-name diagnostic, two
retries were externally terminated and produced no candidate. Cycle 2's log
does not retain its exit or RSS; cycle 3 retains the signal/time/RSS below but
not a reliable outer-wrapper exit status.

The final bounded cycle retained `/usr/bin/time -v` evidence in
`build/native_probe/stage3-fresh/build-cycle3.log`:

```text
Command terminated by signal 15
Elapsed (wall clock) time: 12:51.93
Maximum resident set size (kbytes): 24839624
```

The compiler emitted no error after its initial three source diagnostics, and
the cache contained no completed object. This report does not infer that the
kernel OOM killer sent the signal; the authoritative facts are the measured RSS,
signal 15, absent candidate, and absent compiler diagnostic.

This is a current-source recurrence of the symptom family tracked in
`stage3_frontend_hir_unbounded_memory_growth_2026-08-10.md` (large HIR-phase
RSS followed by external termination). It does not yet prove the same retained
owner or termination mechanism, so that older report remains the investigation
authority and this record binds the Restart-12 reproduction/evidence.

## Exact and adjacent acceptance

1. Profile the current pure-Simple parse/HIR closure and identify the retained
   owner responsible for the growth; do not delete the shared cache or switch
   to the Rust seed.
2. Add an exact full-entry-closure memory regression plus an adjacent bounded
   multi-module build proving that transient module state is reclaimed without
   losing cross-module metadata.
3. Re-run one canonical Stage-3 transaction. It must finish within the selected
   bootstrap RSS budget, emit a provenance-bound candidate, pass sanity, and
   compile/run the hello plus module-qualified field-layout regression.

Three build/fix cycles were consumed in this session. Resume in a fresh scoped
session; do not repeat the unchanged command here.
