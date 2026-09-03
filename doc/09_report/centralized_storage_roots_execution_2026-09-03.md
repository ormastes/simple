# Centralized Storage Roots Execution

**Date:** 2026-09-03  
**Runtime:** `/Users/ormastes/simple/bin/release/macos-arm64/simple`  
**Runtime SHA-256:** `277f8ac9e14ae266ce380a5890d434ce27b47cee9378e2b337cbcc8cd4086767`

The runtime was admitted by `scripts/lib/simple-runtime-provenance.shs`; no
Rust seed, copied binary, or raw-source production wrapper was used.

| Specification | Result |
|---|---:|
| `test/03_system/app/simple/feature/centralized_temp_cache_roots_spec.spl` | 21 passed, 0 failed |
| `test/03_system/compiler/bootstrap_centralized_storage_roots_spec.spl` | 4 passed, 0 failed |

These focused executions prove the two-root contract and the compiler/bootstrap
producer projection. They do not qualify the separately blocked native
Stage2-to-Stage3 producer chain or the Codex watchdog lock-reacquisition lane.
