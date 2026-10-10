# HIR cache release candidate: source-only draft

Status: **DRAFT; native qualification and full verification pending.**
Base: `release/1.0` at `499a4a3b07b2e60f91b4e4a423668dd153c53ba3`.
This candidate has not been compiled or executed. Three prior changed-source
construction cycles were exhausted; preparing this PR did not run another.

## Included changes and source authority

The candidate derives from the cache chain `3fbc908486c` (mandatory integer
writer evidence/regressions), `936e1e6cc43` (typed deterministic dictionary frames and fail-closed
admission), `fe5040cd11e` (nil-miss ownership correction), and `122def17ede`
(typed envelope reader), with their focused regressions and design/evidence.
The earlier `0226af74b95` investigation is retained in the v7 report.

During preparation, release PR #2882 independently landed integer/boolean
serialization and integer-comparator repairs plus failed-store diagnostics.
This candidate preserves its writer file unchanged and retains its comparator
logic. Only the independent merge scratch buffers change in that helper file.
The upstream write/rename failure counters, first-error report and temporary-file
cleanup are retained. The earlier integer writer implementation is therefore
deduplicated rather than replacing the newly released implementation.

Legacy HIR codec advances from v6 to v8; canonical codec stays v4 and its
availability gate stays closed. Writer field order, symbol IDs and all record
contents remain authoritative. Cache publication/load require stable decode and
re-encode; misses retain prior warning roots and always close owned scratch.
Envelope parsing checks split/join identity and preserves the exact HIR suffix.

The release-generated codec is preserved byte for byte after removing the
single new key-order import and 30 sort assignments (20 text, seven SymbolId,
three i64). The release `ConvertCall` schema entry and current field shapes are
unchanged. This candidate does not include optional dictionary-key widening,
the separate MIR text-offset repair, or unrelated root-branch changes.
Generator source and corresponding generated sites are both updated; actual
generator execution/parity qualification remains pending.

## Historical evidence, not evidence for this candidate

| Producer | Observation |
|---|---|
| `e9e8762c79e47d1c0db418d2a8ff5d5eda7b1ef8744ccff32227ae7463926491` | Unboxed integer 3 serialized as nil; native decode failed. |
| `19fcd4ccac312e83cdb4baee72e43398a08b498de98ac9a620c476abc6a49d21` | After integer fix: decode succeeded, re-encode stability failed because native dictionary enumeration changed order. |
| `1fb4606f1131996d178e36881020e657a900b9c37c4142a9d082f854ab353877` | Construction completed; qualification withheld after review found nil-miss promotion would panic. |
| `44a540d538241e202e2dc00440591c4fd9567474706c310f3c75367638325134` | Both real workers reported stable codec bytes; executable printed count=3, but shard-to-final HIR reuse failed. Native warning-envelope cursor ABI rejection was proven. |

The last cold run took 69.43 seconds and 2171392 KiB maximum RSS. It ran a
one-module fixture with an automatic HIR shard and final worker. The final
worker still lowered/stored the module, so no warm-cache or Phase 3 success is
claimed. The envelope parser change has source review/checks only. The reports
preserve exact producer/source identities and local artifact locations:

- `bootstrap_final_worker_frontend_replay_2026-10-11.md`.
- `bootstrap_hir_v7_roundtrip_reencode_2026-10-11.md`.
- `bootstrap_hir_cache_warning_cursor_2026-10-11.md`.
- Design: `doc/05_design/hir_cache_envelope_reader.md`.

## Checks and remaining gates

Source checks cover release-schema preservation, correct helper dispatch at all
30 dictionary sites, actual imports/exports and reader API availability, strict
admission before hit publication, environment-facade guards, patch whitespace,
and the executable-spec directory layout. No tests or native commands ran while
preparing this release candidate. Authored tests cover integer three/bounds,
stable dictionary bytes, decodable unstable-frame refusal, exact body suffixes,
three escaped warnings, stale/missing cache entries and scratch-scope reuse.

Keep the PR draft: generator parity, canonical qualification, native specs,
core/MCP/LSP checks, full tests, Linux/ARM execution, genuine RISC-V qualification
and successful bootstrap Phase 3 remain pending. Do not merge or mark ready on
the basis of the source checks or historical compiler construction receipts.
