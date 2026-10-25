# SMUX Phase 3 major-feature suite and split regression

Date: 2026-10-25. Source baseline: GitHub `release/1.0.0`,
`1e431722b40236eda5e80bd5f5bf06395b0d0d08`.
Worktree: `D:/dev/simple-smux-phase3-suite-20261025`.
Branch: `work/smux-phase3-suite-20261025`.

**TEST_BLOCKED — source authored; no compilation, native execution, case listing,
docgen or zero-stub generator result has been obtained for the new suite.**
Existing historical PASS/FAIL evidence must retain its original producer/source
identity. The 2026-10-18 Phase 2 attempts do not qualify this Phase 3 source.

## Selected scope and existing coverage

The user's selected scope is existing SMUX sessions, detached/background work,
pane splits, layout changes, multiple windows and multiple clients, compiled and
checked with a genuine Phase 3 producer. This is not a new product option.
Requirements remain in `doc/02_requirements/feature/smux_windows_phase3_features.md`.
The older feature plan remains at `smux_windows_phase3_features.md`; this plan
adds a regression and current-source execution traceability without overwriting
its historical results.

| Requested behavior | Existing production evidence owner | Evidence boundary |
| --- | --- | --- |
| Independent sessions, windows, focus, attachment refusal | `smux_service_features_spec.spl` | In-process service state |
| Directional splits and selected-layout transitions | `smux_service_layouts_spec.spl`, `smux_named_layouts_spec.spl` | Service/model geometry, not live terminal output |
| Detached child work and retained shell variables | `smux_windows_conpty_features_spec.spl` | Real ConPTY; capture polling actively drains output |
| Unattended background output, real child size and session isolation | `smux_windows_owner_lifecycle_spec.spl` | Actual external owner/child lifecycle |
| Key decoding and copy navigation | `smux_client_input_spec.spl`, `smux_client_copy_input_spec.spl` | Decoder state/actions |
| Client-local windows, frame validation, canvas arbitration | `smux_interactive_protocol_spec.spl`, `smux_interactive_client_sizes_spec.spl` | Actual dispatcher/service; no independent consoles |
| Real interactive clients and sibling continuity after detach | `smux_windows_shared_clients_spec.spl`, `windows_smux_interactive` native fixture | Actual product/fixture binaries and external containment required |

Do not add wrappers around those wrappers or duplicate their independent checks.
No tmux executable substitutes for SMUX. No positive clipboard mutation is part
of this regression; a separate explicit user action is needed for that gate.

## Concrete gap and new production assertions

At the baseline, `interactive_client.apply_action` performs a directional split
then calls arrange. `client-layout ... current` and frame reflow map the service's
invalidated `manual` layout to `tiled`. Two tiled panes become columns, so the
upper/lower direction requested by Ctrl-B quote is lost. Existing decoder and
standalone split tests can both pass without detecting this composition error.
The current live interactive fixture drives Ctrl-B percent, which does not expose
the horizontal-to-column conversion.

New executable: `test/03_system/tools/smux_major_features_phase3_spec.spl`.
New mirror: `doc/06_spec/03_system/tools/smux_major_features_phase3_spec.md`.

| New scenario | Requirement mapping | Distinguishing oracle |
| --- | --- | --- |
| Horizontal split, current layout, repeated frames | CORE-002, INTERACTIVE-001/003 | Same pane IDs retain full-width top/bottom rectangles and one separator row |
| Vertical split followed by explicit named layout | CORE-002/005, INTERACTIVE-001 | Frame keeps left/right split; explicit `even-vertical` then produces full-width bands with unchanged IDs |
| Targeted nested split with sibling frame and detach/reattach | CORE-001/004, INTERACTIVE-003 | Splitting the left pane preserves the right pane; foreign-pane refusal, inactive-window focus and other-session geometry survive |

The tests execute the real decoder, service and interactive dispatcher directly.
They allocate no child and do not call the private terminal controller or replace
its transport. Service split calls deliberately isolate the geometry interaction;
they are not evidence that `client-split` spawned a shell or that a keyboard
action reached an independently rendered terminal. The production repair owner
must retain durable manual rectangles, including nested geometry, and adapt the
existing tests that expected all manual rectangles to disappear. Explicit named
layout selection must continue to replace manual geometry intentionally.

## Native execution gates

Root owns producer provenance, resource scheduling and the production repair.
Before execution, record the genuine Phase 3 compiler/full-CLI identity, source
snapshot, matching runtime/provider capsule, backend, target, exact argv and
private cache/output paths. A file named `phase3` or an older Phase 2 admission
is insufficient. Preserve unrelated dirty files and materialized links.

The existing native test route is mandatory; no new runner framework is needed:

```text
<admitted-phase3-cli> test test/03_system/tools/smux_major_features_phase3_spec.spl --native-backend=llvm --native-source src/providers/windows_native/lib --native-source src/app --native-source src/lib --native-source src/os --native-source src/compiler --keep-artifacts --verbose
<admitted-phase3-cli> spipe-docgen test/03_system/tools/smux_major_features_phase3_spec.spl --output doc/06_spec --no-index
```

Apply the parent campaign's finite process-tree memory/time limits outside the
runner. Preserve binary-owned listing, actual case/assertion counts, terminal exit,
quiescence, stdout/stderr and generated native artifact identity. Do not treat
source case counts or `--list` alone as executed evidence. No JSON format is
selected by default; new structured campaign records use SDN, while existing
required receipt formats and historical evidence remain unchanged.

Run each affected criterion once after a material repair. Count previous cycles
toward the user-mandated hard six-cycle limit; a different output directory or
worktree does not reset it. Record blocked/skipped/unexecuted counts honestly.
Do not repeat already-green unrelated suites. Docgen must report completion and
zero stubs before the authored mirror is called generated/verified.

The full requested major-feature acceptance remains open until real SMUX build,
product sanity and relevant existing live-owner/client suites execute on the
admitted Phase 3 producer. The three new geometry cases close one regression,
not the full live-host acceptance boundary.
