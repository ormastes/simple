# Kernel Plugin Migration Phase 1/2/4 Executable Matrix

**Date:** 2026-09-03  
**Integration base:** `7ca7bde34c2`  
**Runtime:** `/Users/ormastes/simple/bin/release/macos-arm64/simple`  
**Runtime SHA-256:** `277f8ac9e14ae266ce380a5890d434ce27b47cee9378e2b337cbcc8cd4086767`  
**Admission receipt:** `scripts/lib/runtime-provenance/277f8ac9e14ae266ce380a5890d434ce27b47cee9378e2b337cbcc8cd4086767.env`

## Result

| Phase | Executed evidence | Status |
|---|---|---|
| 1 | Typed-HIR ABI field append/rename/retype/reorder sensitivity, body insensitivity, and field-type comparison | PASS |
| 2 | Append-only V1→V2 compatibility, reordered ordinal rejection, and app-boundary environment decoding | PASS |
| 4 | Canonical negotiation and existing lint-table assertions | PASS |
| 4 mutation | Add one provider file and table row, then remove only the row | Added-row PASS; removal rerun exposed stale test-cache reuse |

The Phase 4 supervisor now changes the probe revision after removing the row so
the mutation cannot be accepted through an unchanged-test cache hit. That final
fix was not rerun in this session because the mandatory three-cycle limit had
been reached. It remains a required fresh-session verification gate.

## Contract changes

- Static lint providers now pass through the shared `negotiate` contract before
  dispatch rather than maintaining a second name/major/digest decision path.
- The matrix admits the runtime through its immutable pure-Simple receipt before
  invoking any SPipe test.
- Phase 2 no longer invokes a raw `.spl` checker through `simple run`; it executes
  the typed SPipe contracts through the admitted runtime.
- Successful receipts are emitted by the supervising matrix after the test
  process succeeds, avoiding reliance on test-runner display of passing prints.

## Commands

```text
KPM_SIMPLE_BINARY=/Users/ormastes/simple/bin/release/macos-arm64/simple \
KPM_RUNTIME_PROVENANCE_ROOT=$PWD \
sh scripts/check/check-kernel-plugin-migration-evidence-matrix.shs --phase 1

KPM_SIMPLE_BINARY=/Users/ormastes/simple/bin/release/macos-arm64/simple \
KPM_RUNTIME_PROVENANCE_ROOT=$PWD \
sh scripts/check/check-kernel-plugin-migration-evidence-matrix.shs --phase 2

KPM_SIMPLE_BINARY=/Users/ormastes/simple/bin/release/macos-arm64/simple \
KPM_RUNTIME_PROVENANCE_ROOT=$PWD \
sh scripts/check/check-kernel-plugin-migration-evidence-matrix.shs --phase 4
```

No Rust seed, raw-source production wrapper, bootstrap provenance path, Phase 7
surface, tooling daemon, or generic KPF runtime was used or modified.
