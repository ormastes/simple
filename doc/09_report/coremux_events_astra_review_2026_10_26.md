# Event journal independent Astra source review — 2026-10-26

**CURRENT STATUS: V3 focused source review accepted; the V2 P2 is closed at source. All execution NOT_RUN.** The V2 finding and pins below remain historical; the V3 resolution is appended. No author file was edited and no compiler/test/native process ran.

V2 review: WARN, one P2 source finding. Reviewed the four-path freeze `build/review/coremux-events-source-v2.sdn` against the small-module guide, frozen event/wire contracts and owned array runtime. All four SHA256 values matched.

## P2: failed array growth can advance a poll cursor without its event

At `src/os/apps/smux/core_mux_events.spl:134`, `selected.push(event)` has no success/cardinality check. Line 136 advances `finish` regardless. If allocation fails, the returned batch can omit the event but advertise its cursor at line 141 with `reconciliation_required=false`. A consumer continuing from that cursor silently loses the observation. Whole-batch byte sizing does not detect the absent record.

The same class affects the singleton `[event]` at line 87, retained copy/append at lines 99–100, and final retained slice at line 110. Canonical event validation permits empty batches, so a failed singleton can bypass observation validation; failed retained growth/slicing can return a journal whose last cursor no longer matches its retained tail.

Owned source evidence: `src/runtime/simple_core/core_array.spl:905` returns zero when its array is invalid or reserve fails; `rt_array_push` at line 915 forwards that status. The source does not inspect push success or compare expected cardinality. This is a source-derived failure path, not an executed OOM reproduction. Declaring OOM recovery unqualified does not make successful silent cursor advancement valid.

Required repair: check independently expected cardinality after every singleton/copy/append/slice/result-array construction before exposing a result or advancing a returned cursor. Use typed Unavailable/NotApplied on mismatch; final returned journal/batch checks must preserve contiguity and returned-cursor correspondence. Add deterministic production mismatch admission controls without claiming actual allocator fault injection. Preserve the input journal by retaining the V2 fresh-copy strategy.

## Other reviewed behavior

- Exact binding compares owner ID, generation and lease token; shape validation grants no authority. No hidden authentication, renewal, polling, process access or registry appears.
- Serial preflight checks `count <= MAX-last` before addition, including count zero at MAX. Retention validation avoids `previous+1` overflow. No signed narrowing of cursor values appears.
- Count/byte eviction and individually oversized valid events advance the explicit loss floor. Polls before that floor require reconciliation; pagination otherwise stops at the last selected event. These normal paths are coherent, subject to the allocation finding.
- Byte accounting uses the canonical conservative event bound plus two array-separator bytes and full empty-batch overhead. Existing u64/bool sizing is fixed, making cursor-independent overhead valid. The 256 minimum is not falsely promised sufficient for all handles: construction checks actual conservative empty-batch size. The bound excludes the outer wire envelope and allocator overhead, as documented.
- Future cursors return InvalidRequest, consistent with the current source/report's invalid-cursor behavior; no frozen contract requires InvalidTarget. Live poll byte pressure uses Busy. The spec mostly asserts `is_err()` rather than exact error kind/NotApplied; stronger typed negative oracles would prevent future regressions.
- Ten authored SSpec cases call production functions with literal cursor expectations. Two compare actual canonical serialization against its conservative budget. No mock native events, zero-case pass or executable placeholder is present. The manual accurately marks these authored/unrun controls and does not claim real authentication or child observations.

## Exact V2 pins

| Path | SHA256 |
|---|---|
| `src/os/apps/smux/core_mux_events.spl` | `4fde0314eded2818cd6ef89e0be9a4ec6bb1962d9b8bf09d375015cee1323d89` |
| `test/01_unit/os/apps/smux/core_mux_events_spec.spl` | `e1dfafc3d65fe6aa3f437c7b9850c64bdc798a55e75db227851fdf6faf84f832` |
| `doc/06_spec/01_unit/os/apps/smux/core_mux_events_spec.md` | `20994995d035ff996f2fd7da59f1fa1458c990b5d888db60d888037506734d3b` |
| `doc/09_report/coremux_events_source_2026_10_26.md` | `ca5253f4829546869729c966d20430db734ff7e9e6c9d3395f115e0b3aec7a4d` |

Ten cases authored, zero executed. Compilation, SSpec/docgen, actual allocation faults, native effects, performance, owner integration and full-provider qualification remain NOT_RUN. This review does not admit the frozen candidate as allocation-safe. The P2 was sent to author/root before this report.

## V3 focused resolution

Reviewed only the identified construction paths and their source/spec/manual/report changes in `build/review/coremux-events-source-v3.sdn`; all four SHA256 values matched. **The V2 P2 is closed at source; no remaining finding in this bounded follow-up scope.** This is not a native allocation-safety or complete-provider qualification.

The singleton has an exact one-element check at source line 88 before event validation. Each retained copy checks a one-element increase at line 105; append checks the independently expected total at line 108. The retained slice checks its exact expected tail length at line 119; the constructed journal passes the existing contiguity/shape/budget validation at line 123. Poll checks selected-array growth at line 151 before byte accounting or advancing `finish` at line 154. Final batch cardinality and canonical event validation at line 156 provide an additional return-path check. These mismatch branches return Unavailable/NotApplied without replacing the original journal.

The existing invalid-state scenario gained missing-tail and duplicate-cursor controls through production admission. These exercise structural rejection, **not** the new allocation-failure branches or real allocator exhaustion; that coverage remains unmeasured and the manual/report say so. The author also clarifies that helper NotApplied cannot erase an integrating owner's already-observed external Partial/Unknown effects. No broader source sweep or execution was performed.

| V3 path | SHA256 |
|---|---|
| `src/os/apps/smux/core_mux_events.spl` | `7ac8c77508b66c8a03cf86f623678de7e3b410f58575d4dda916e235e86af14a` |
| `test/01_unit/os/apps/smux/core_mux_events_spec.spl` | `243c6d7123c7a03daa180342564b4ba223650a06c1fb89ff40f993125ad6fffa` |
| `doc/06_spec/01_unit/os/apps/smux/core_mux_events_spec.md` | `0631e94498a2d93e447e7133dbd69b6ca979c08e658654ac4b6741b237849d4b` |
| `doc/09_report/coremux_events_source_2026_10_26.md` | `486a27419ed8f9294e4b09dea065e388cb3828ed9cf912d27eb38828118d9b8b` |

V3 remains ten authored cases, zero executed. Compiler/build/test/docgen/native work: NOT_RUN. Author files unchanged by reviewer. V1/V2 manifests and findings remain historical evidence; this source acceptance does not imply full CoreMux admission or release readiness.
