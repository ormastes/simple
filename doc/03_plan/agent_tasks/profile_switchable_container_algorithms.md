# Agent task ownership: profile-switchable containers

| Lane | Owner | Scope |
|---|---|---|
| Source attribute and typed CollectionPlan | Codex | Parser, HIR, semantic guards, MIR lowering, explanation. |
| Runtime representations | Codex | Generic set/map families, transitions, observations, value/order safety. |
| `.sprof` v2 and CLI | Codex | Metric records, admission, aggregation, file workflow. |
| Cross-engine SPipe and performance | Codex | Executable/manual evidence and NFR measurements. |
| Lower-model sidecars | N/A | No sidecar assigned in this lane. |

Merge owner: Codex. Final reviewer: Codex at normal/highest capability after executable evidence exists. Shared interface names: `AdaptiveSetAttribute`, `AdaptiveSetWorkloadProfile`, `SprofCollectionLoad`, `CollectionPlan`; no silent placeholders are permitted.

## Bounded continuation, 2026-10-16

[Current reconciliation and dependency handoff](../../09_report/item7_bounded_continuation_2026-10-16.md):
PR #3073 is merged into `release_phase3`, but Item 7 remains incomplete and
TEST_BLOCKED. The shared Phase3 cycle 2 has three HIR failures and no executable.
Its 1,328 cached HIR successes are not runtime acceptance. The fresh Item 7
continuation starts no duplicate compiler build and preserves concurrent Item
2/4 and Phase3 work. Resume the remaining gates only with the required qualified
runner; historical routing/Hello passes must not be relabeled Phase3 PASS.

## Isolated completion session, 2026-10-03

Target: `release/1.0`, starting at `eedaa197ae4c16442879607e7dee35c8863691f5`.
Integration owner: Codex root, session `01a1005f-49d0-7c31-9855-1ff9bfa7ff71`,
worktree `C:/dev/simple-item7-completion-20261003`, branch
`work/item7-completion-20261003`. Integration uses a reviewed PR; no direct
release-ref update or publication is part of development.

| Parallel owner | Separate worktree | Owned change |
|---|---|---|
| research_design | `C:/dev/simple-item7-research-20261003` | Research supplements, architecture, detail design; independent source review of root changes. |
| acceptance_tests | `C:/dev/simple-item7-acceptance-20261003` | PSC-AC-001..008 matrix, executable system scenarios, model fixture, matching manual; runtime qualification. |
| compiler_implementation | `C:/dev/simple-item7-compiler-20261003` | Typed factory validation, declaration metadata transport, compiler tests. |
| root | Integration worktree above | Profile admission/selection consistency, integration, final verification and landing. |

Shared acceptance IDs `PSC-AC-001` through `PSC-AC-008` map to the corresponding
selected `REQ-PSC` requirements. New model helpers use `psc_acceptance_`.
The independent model uses arrays, checks every operation, and never treats an
adaptive implementation as its oracle. Missing runtime qualification is a
failed admission gate, not a skipped passing scenario.

Tests were written before the root profile fix and typed factory implementation,
but neither execution RED nor GREEN has been established. Both inspected Windows
executables report a Rust-seed banner; `bin/release` and a configured qualified
runtime are absent. WSL/bootstrap discovery continues. All source-only review
results remain distinct from executable acceptance. The user selected best-effort
resource measurements on 2026-10-03; numeric latency/memory thresholds are not
mandatory. Full correctness and execution qualification remain open.

Root source review found that prepared-profile selection discarded measured
collision evidence and preparation converted malformed pairs into absent data.
The fix preserves invalid/absent/zero distinctions and reuses runtime admission
validation in CLI explanation. Regression cases cover prepared/one-off decision
parity, stale caller facts, missing and mismatched metric pairs, and explanation
rejection. This repair does not close typed lowering or full P6 instrumentation.

## Remaining capture implementation sequence

### Parallel continuation and stable landing, 2026-10-03

The independently tested watchdog cancellation repair and Windows admission
correction landed in [PR #2345](https://github.com/ormastes/simple/pull/2345),
merge commit `812304cc2d30beffd5acf1a0ee273de54463a82c` on `release/1.0`.
Actual evidence covers controller loss, ordinary completion, completion races,
deadline/TERM-grace behavior, and emulated unsupported-Windows admission. This
does not establish a completed bootstrap or an item 7 verification PASS.

Parallel coding added the caller-owned filter completion API and standalone
native artifact receipt publication. Their unit tests remain unrun. Source
review repaired receipt cleanup before ownership, unwanted same-path no-op
rebuilds, and rejection of budgeted builds with no reported plans. These changes
remain local; only the tested watchdog repair was pushed and merged. A bounded
search found no newly qualified runtime in the known Windows/WSL lanes. The
full item 7 implementation, execution evidence, and release landing remain open.

Progress update, 2026-10-03: the sequence below is now an execution checklist,
not a claim that all code remains unwritten. The integrated branch contains
run capture/replay orchestration, interpreter argument transport and canonical
extern dispatch, failure cleanup, output admission, and executable regression
scenarios. These changes have source review only; their runtime evidence remains
pending. Five extended metrics still need actual observation wiring rather than
serializer-only support. Full typed profile selection and generic physical
lowering remain incomplete.

Native-build policy and memory-budget controls now share strict parsing and
cache identity. Typed explanation uses a compiler-produced MIR receipt API;
its compiler implementation and target restrictions must be verified together.
The first literal membership slice does not establish complete collection
planner coverage. No RED/GREEN execution, verification PASS, or release landing
is claimed by this session's local commits.

1. Define one bounded execution-owned `collection_capture_begin`, `note_size`, `note_lookup`, `finish`, and `abort` contract. The interpreter and native runtime must share its event semantics; the app must receive a snapshot after evaluation. An app-only Simple global cannot observe the interpreter's fresh module context.
2. Instrument attributed text and generic map/set operations once per logical event. Generic set delegates to generic map; do not count both layers. Keep lookup hit detection independent of an optional map value, preserve lifetime peak across `clear`, and filter events by admitted target/site.
3. Add `simple run --collection-profile-out=PATH` with required workload and target identifiers. Serialize the bounded snapshot through the existing `.sprof` v2 writer after execution; never open files in collection operations. Make snapshot/write failures visible and clear run state on every exit path.
4. Run a first workload, change only its algorithm attribute, load the emitted profile in a second workload, and verify exact-site reuse plus path/source/workload/target rejection. Then run interpreter/native differential and NFR checks on an admitted pure-Simple runner.
