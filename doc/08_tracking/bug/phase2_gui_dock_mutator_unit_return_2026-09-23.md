# Phase2 dock panel model and mutator return

Source base: `e6ffda6849e6aa7fe01a7d23ddc71e9773286532`.
Worktree: `/Users/ormastes/simple-tmp/gui-dock-mutator-unit-20260923`.
Focused native behavior: PASS, 11 checks. Independent Astra review: PASS
(`/root/stage2_after_lexer_cleanup/dock_mutator_review`), no blocking findings.
Full CLI, compiler matrix and bootstrap admission are not claimed here.

## Prior model evidence

This incorporates the unaccepted typed dock patch from
`/Users/ormastes/simple-tmp/phase2-gui-shell-type-20260923`, whose report is
`doc/08_tracking/bug/phase2_gui_dock_model_type_gap_2026-09-23.md`.
The GUI called panel collection methods absent from canonical DockLayout;
DockPanel and the numeric zone constants were also absent. Its hit-test
projection reproduced Text/Int HIR rejection with
`ANY/id -> LOCAL-BEST idx=0 count=4`, borrowing DockZone's numeric ID.
The typed model cleared that rejection but its behavior fixture trapped.

Both GUI copies now import DockPanel and the three existing numeric zone
identities, and explicitly type the queried arrays. The canonical model owns
text panel identity, display metadata, zone and visibility. It implements the
already-used add/remove/query/select methods, preserves order and selection
on same-zone replacement, and clears selection on hiding, movement or removal.
Invalid additions/selections preserve state. Toggles carry every model field;
legacy show_right/hide_right semantics are retained.

## Distinct mutator cause and fix

The prior native binary SHA256 was
`1f799d36ece96fcefdbf4588c56664df0e383b8f59e982b9def6277fc34a7650`.
LLDB retained `udf #0xc11f` at `DockLayout.add_panel+1092` on replacement.
Both bare-return branches lead to generated traps. The append path instead
returns its panel-array receiver in x0 after push, proving that the omitted
signature admitted a non-unit tail result inconsistent with bare returns.
This is return inference, not evidence of lost receiver mutation.

The sole correction relative to the prior model is explicit
`me add_panel(panel: DockPanel) -> ()`. This declares the method's existing
side-effect-only API. No algorithm, iteration, allocation or object layout
changes relative to that typed model. New disassembly contains proper return
epilogues on all three paths and no UDF instruction in add_panel.

## One fresh verification cycle

Admitted Stage2 producer:
`/Users/ormastes/simple-tmp/macos-bootstrap-restart-20260922/build/bootstrap/macos-enforced-bd544-stage2/stage3/aarch64-apple-darwin/stage2-admitted/simple`.
SHA256 `0c65162af9c89bdb9c6583ca91820f795231c9bf4c451b6a69ea66794c66c084`
matches its sibling `admission.env`. The matching frozen runtime capsule was
verified before use. Supported command: native-build. No Rust seed used.

Evidence lives under `build/native_probe/dock-mutator/` in this worktree.
`build-green.sh` records the exact invocation. The shard copies the complete
canonical dock_zone source and checked-in fixture byte for byte. Build used
two threads, isolated cache/output and SIMPLE_NO_STUB_FALLBACK=1 under the
5859375 KiB sampled watchdog, with 180s build and 30s runtime deadlines.

| Evidence | Result | Time | Maximum RSS |
|---|---|---|---|
| Prior typed model runtime | SIGILL/132 | 0.35s | 8,732,672 bytes |
| Corrected build, 2 modules | 2 compiled, 0 failed | 2.91s | 156,499,968 bytes |
| Corrected runtime | 11 checks, exit0 | 0.34s | 8,896,512 bytes |

The runtime difference is +160 KiB (+1.9%) in one short process and is not a
statistical regression claim or speedup claim. The fixed run completes all
checks, whereas the baseline stops during check2; workloads are unequal.
The existing model remains O(n) for query/add/remove/select and O(1) for
toggles. Guard receipts show quiescent1, observer_errors0 and overruns0.
The guard is sampled enforcement, not kernel hard containment.

The fixture validates initial order/visibility; replacement and selection;
invalid additions and selections; invalid zones; movement; hiding; legacy
right visibility; state-preserving toggles; missing/present removal; bottom
selection and removal. Its only success output is
`editor-dock-panels: 11 checks passed` after every conditional assertion.

## Boundaries

The generic compiler diagnostic for contradictory inferred return paths is
not repaired here; this mutator now expresses its intended unit contract.
The pre-existing GUI drag persistence/stale-ID behavior is a separate lane.
This change does not claim to fix local dock writeback through controller and
session, to prove live GUI operation, or to admit full Phase2/Stage3.
General compiler/lib/MCP verification awaits the source-matched full CLI and
test runner. No bootstrap or push was performed.
