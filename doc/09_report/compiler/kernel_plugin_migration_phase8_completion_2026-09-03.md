# Kernel Plugin Migration Phase 8 Completion Evidence

**Date:** 2026-09-03  
**Verdict:** SOURCE COMPLETE; EXECUTABLE QUALIFICATION BLOCKED

## Evidence rows

| Criterion | Status | Evidence |
|---|---|---|
| Deterministic caret/tilde selection and lexical equal-version tie break | PASS | `src/app/pkg/requires_range.spl`; `test/00_unit/scripts/kernel_plugin_phase8_source_contract_test.shs` |
| Root `simple lock` and `simple update` compiled dispatch | PASS | Root CLI imports and calls `run_lock_command` / `run_update_command`; raw-source delegation is rejected by the source contract. |
| Unsatisfied range and rejected policy preserve admitted lock | PASS (source/test contract) | Resolution and policy validation precede `file_atomic_write`; system mutation remains executable-runtime blocked. |
| Atomic lock/update publication | PASS (source contract) | Both production entrypoints publish through `file_atomic_write`. |
| Manifest identity | PASS | Lock receipt binds `plugin_manifest_policy: simple-sdn`, `plugin_manifest_location: simple.sdn`, and `simple_abi_policy: v1`; alternate manifest paths fail closed. |
| Phase 8 source contract | PASS | `sh test/00_unit/scripts/kernel_plugin_phase8_source_contract_test.shs` |
| Phase 8 executable unit/system specs | BLOCKED | No admitted non-seed pure-Simple runtime exists in the current integration workspace. The probe exited before executing product behavior. |
| Phase 4 stale remove-row cache regression rerun | BLOCKED | Fresh `--phase 4` attempt exited `2`: admitted pure-Simple runtime unavailable. No cached PASS was reused. |
| Ordering after Phase 7 | BLOCKED | Phase 7 one-binary, dynload, parity, and provenance-bound deployment qualification remain incomplete; Phase 8 cannot be declared migration-complete before that gate. |

## Changes

- Added argument-taking compiled entrypoints for `lock` and `update` while retaining standalone `main` wrappers.
- Replaced root CLI raw-source delegation for those commands with direct compiled calls.
- Added canonical manifest-location identity to the generated lock receipt.
- Strengthened the migration matrix to reject raw-source root dispatch and require atomic publication seams.
- Fixed Phase 8 runtime admission propagation so an unavailable runtime fails once instead of cascading into a copy attempt.

No Rust seed, raw-source production wrapper, copied unauthenticated compiler, or synthetic runtime receipt was used.
