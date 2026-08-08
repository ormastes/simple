<!-- codex-architecture -->
# Office CLI, Calc TUI, and Semantic UI Access Architecture

## Status

Implemented for the explicitly selected F1 feature option and N1 quality
profile. The final requirements, implementation, focused tests, gate, and
generated manual are present. This design remains the ownership contract; it
does not authorize a parallel Office automation protocol.

## Decision

Expose Calc through the deployed command:

```text
simple office calc [FILE] --tui
```

The deployed `simple ide --feature-check --tui|--gui` and `simple office`
commands receive startup-light CLI ownership before global option filtering.
Calc composes its existing sheet model, formula evaluator, real ANSI TUI, and
the existing UI access session/service. Operators and LLM tools use the
canonical flow:

```text
windows -> snapshot -> surface -> find -> act -> history
```

The access surface is `main`. Its frozen minimum node identities are:

```text
main
main#cell_A1
main#formula_input
main#confirm_edit
```

Cells use `main#cell_<A1-reference>` consistently. The controller rebuilds one
semantic tree after each accepted state transition, advances the snapshot
revision, and records correlated request/action/result events in the existing
bounded history owner.

`AVG(...)` is a formula-parser compatibility alias that canonicalizes to
`AVERAGE(...)`. Multiplication remains owned by the existing expression
evaluator. Neither behavior is reimplemented in the controller or UI adapter.

<!-- sdn-diagram:id=office_cli_tui_ui_access.architecture -->
<details class="sdn-source"><summary>SDN source</summary>

```sdn id=office_cli_tui_ui_access.architecture hash=sha256:auto render=ascii
@layout dag
@direction LR
SimpleCLI -> IdeCliEntry
SimpleCLI -> OfficeCliEntry
OfficeCliEntry -> CalcController
CalcController -> SheetModel
SheetModel -> FormulaEvaluator
CalcController -> CalcTuiRenderer
CalcController -> UISession
UISession -> UiAccessService
SimpleUiCLI -> UiAccessService
UiAccessService -> AccessStore
SystemSpec -> DeployedCommands
DeployedCommands -> SimpleCLI
SystemSpec -> EvidenceBundle
CalcTuiRenderer -> EvidenceBundle
UiAccessService -> EvidenceBundle
```

</details>
<details class="sdn-ascii" open><summary>Diagram</summary>

```ascii generated-from=office_cli_tui_ui_access.architecture hash=sha256:auto
simple CLI -> IDE entry
          -> Office entry -> Calc controller -> sheet -> formula evaluator
                                           -> real ANSI TUI
                                           -> UI session -> access service -> bounded store
simple ui -----------------------------------------------^
system spec -> deployed commands + TUI/protocol/artifact evidence
```

</details>
<!-- sdn-diagram:end -->

## Layer Ownership

| Concern | Owner | Constraint |
|---|---|---|
| Unified dispatch | startup-light CLI entry modules | Preserve Office/IDE arguments until their owner parses them |
| Command grammar | Office and IDE CLI entry modules | Preferred Calc spelling is `office calc [FILE] --tui`; preserve legacy aliases |
| Sheet state | existing `Sheet`/workbook modules | Single authoritative values, formulas, cached display, and save state |
| Formula semantics | existing formula evaluator | `*` remains expression syntax; `AVG` forwards to `AVERAGE` |
| Interaction orchestration | Calc controller | Own selection, edit buffer, confirmation, recalculation, tree rebuild |
| Semantic model | common UI tree/session and access contract | No Office-only snapshot/action schema |
| Live transport | existing UI test/access service | Loopback service, revision validation, correlated requests |
| History | existing access store/session | Maximum 64 events per active surface/session |
| ANSI rendering | Calc access controller | Render the established 20x30 sheet viewport in a deterministic 124x37 frame |
| Test-only queries | SGTTI in executable tests only | Production Calc closure must not import or construct SGTTI |

## Adapter Choice

F1 is a runtime adapter composition, not a compiler feature transform:

- the Calc controller adapts app-local sheet transitions to `UISession`;
- the access service adapts the session to the existing
  `simple.access/v1` CLI protocol;
- the real TUI adapts the same controller state to ANSI output.

No MDSOC weave is needed. UI access is explicitly launched and does not impose
snapshot construction, polling, or capture allocation on ordinary non-debug
Office commands.

## Semantic Contract

The `main` surface has app identity `office-calc`, mode `tui`, a root node, a
formula input, a confirmation control, and stable cell nodes for the visible
grid. Required node properties include:

| Node | Kind | Required state/properties | Actions |
|---|---|---|---|
| `main#cell_A1` | `gridcell` | reference, display value, raw/formula value, selected, focused | `select` |
| `main#formula_input` | `textfield` | current input value, active reference, editing | `type_text`, `set_value` |
| `main#confirm_edit` | `button` | enabled while an edit is pending | `invoke` |

Value-bearing actions use the existing typed access request payload. The
deployed CLI extends `simple ui act` with an argument-safe text-value option;
it must not concatenate a shell command. The request includes the observed
revision and a correlation/request ID.

Accepted confirmation follows this order:

1. validate surface, canonical target, action capability, and revision;
2. update the controller edit state;
3. commit through `Sheet.set_value`;
4. recalculate through `recalculate_formula_cells`;
5. rebuild the semantic tree and ANSI frame from the new sheet;
6. increment the revision;
7. record request, action, and result events with the same correlation ID.

Rejected actions do not mutate the sheet, revision, render frame, or history
except for a bounded rejection result when the common protocol requires it.

## Formula Boundary

The acceptance witness is intentionally small and exact:

```text
A1 = 6
A2 = 8
B1 = =A1*A2       -> 48
C1 = =AVG(A1:A2)  -> 7
```

The `AVG` alias canonicalizes before normal dispatch, so argument collection,
range traversal, empty-range behavior, and error semantics remain identical to
`AVERAGE`. The raw formula text remains `=AVG(A1:A2)` for display/export unless
the existing formula serialization owner already canonicalizes names.

## Startup and Hot Paths

- The unified CLI must dispatch Office and IDE before global filtering removes
  owner-specific options.
- Production wrappers execute cached compiled artifacts; raw `.spl` entrypoint
  fallback and Rust-seed delegation are forbidden.
- The rendered snapshot and TUI expose the visible 20x30 grid. The mutable
  `UISession` action tree intentionally contains only the formula controls and
  addressed fixture cells, preventing every edit from rebuilding 600 buttons.
- `find` queries inspect the current bounded snapshot; they do not rebuild or
  rescan the filesystem.
- Actions rebuild at most one visible semantic tree and one TUI frame.
- No request handler may spawn a subprocess, sleep/retry, or reread the workbook
  from disk.
- Save/reopen is an explicit artifact scenario, not part of every action.

## Cache and Invalidation

The current semantic snapshot and rendered TUI frame may be cached by revision.
Selection, edit-buffer changes, confirmation, workbook load, and visible-range
movement invalidate the affected cache. A rejected stale/invalid request does
not invalidate it. The access store is append-bounded to 64 events and never
acts as a command queue when used in read-only fallback mode.

## N1 Quality Contract

On the checked-in realistic fixture:

- warm Calc ready within 2 seconds;
- warm `windows`/`snapshot` p95 at or below 100 ms;
- warm `find` p95 at or below 25 ms;
- action plus independently observed post-state p95 at or below 250 ms;
- access-layer RSS delta at or below 20 MiB;
- deterministic 124x37 capture;
- terminal state restored on every exit;
- protocol/history bounded and deterministic.

## Failure Policy

- Unknown Office/IDE options return `invalid_argument` and nonzero status.
- Missing files report a typed diagnostic; an omitted Calc file creates a new
  workbook.
- Stale revisions return `stale_target`.
- Missing canonical IDs return `target_not_found`.
- Unsupported actions return `unsupported_action`.
- Invalid formulas render the existing Calc error state and never fabricate a
  numeric result.
- Service shutdown makes live access return `source_unavailable`.

## Verification Boundary

The app-development gate runs once through the existing Simple runtime and
writes a suite receipt plus TUI/protocol evidence. The SSpec verifies those
artifacts in-process, avoiding nested interpreter recompilation. A deployment
rebuild is a separate release concern and is not required to validate an
Office application change.

Test-only orchestration and SGTTI may exist in the executable spec/check gate.
The normal Office entry, Calc controller, real TUI, IDE entry, and unified CLI
must exclude `std.ui_test.sgtti`, `SgttiTestDriver`, and test-only snapshot
construction.

## Consequences

Positive:

- one operator protocol serves GUI/TUI debugging and LLM communication;
- formulas are proven through the real application state;
- other Office apps can adopt the same controller adapter later;
- semantic assertions and screen evidence remain independent.

Tradeoffs:

- Calc controller/session wiring touches several existing owners;
- value-bearing CLI actions expand the common access CLI contract;
- the initial PTY/capture evidence is primary-host scoped under N1.

## References

- `doc/01_research/local/office_cli_tui_ui_access.md`
- `doc/01_research/domain/office_cli_tui_ui_access.md`
- `doc/02_requirements/feature/office_cli_tui_ui_access.md`
- `doc/02_requirements/nfr/office_cli_tui_ui_access.md`
- `src/app/office/interactive.spl`
- `src/app/office/sheets/sheets_app.spl`
- `src/app/ui/access_cli.spl`
- `src/lib/common/ui/access.spl`
